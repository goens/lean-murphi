namespace Murϕ

abbrev ID := String
abbrev BinOp := String
-- Binops: ?: -> | & ! < <= = != >= > + - * / %

mutual

inductive Decl
  | const : ID → Expr → Decl
  | type  : ID → TypeExpr → Decl
  | var   : List ID → TypeExpr → Decl

inductive TypeExpr
  | previouslyDefined : ID → TypeExpr
  | integerSubrange : Expr → Expr → TypeExpr
  | enum : List ID → TypeExpr
  | record : List Decl → TypeExpr -- Note: this is more premissive than the grammar, should be ok though
  | array : TypeExpr → TypeExpr → TypeExpr
  deriving Inhabited

inductive Formal
  | mk : Bool → List ID → TypeExpr → Formal
  deriving Inhabited

inductive ProcDecl
  | procedure : ID → List Formal → List Decl → List Statement → ProcDecl
  | function : ID → List Formal → TypeExpr → List Decl → List Statement → ProcDecl
  deriving Inhabited

/-
 I have no idea what an "actual" is, the manual doesn't describe it either.
 Otherwise, the `call` constructor should be something like:

   | call : ID → List Actual → Expr
-/
inductive Expr
  | designator : Designator → Expr
  | integerConst : Int → Expr
  | call : ID → List Expr → Expr
  | universal : Quantifier → Expr → Expr
  | existential : Quantifier → Expr → Expr
  | binop : BinOp → Expr → Expr → Expr
  | negation : Expr → Expr
  | conditional : Expr → Expr → Expr → Expr
  deriving Inhabited

inductive Designator
| mk : ID → List (ID ⊕ Expr) → Designator
deriving Inhabited

inductive Quantifier
  | simple : ID → TypeExpr → Quantifier
  | assign : ID → Expr → Expr → Option Expr → Quantifier
  deriving Inhabited

inductive Statement
  | assignment : Designator → Expr → Statement
  | ifstmt : Expr → List Statement → List (Expr × List Statement) → List Statement → Statement
  | switchstmt : Expr → List (List Expr × List Statement) → List Statement → Statement
  | forstmt : Quantifier → List Statement → Statement
  | whilestmt : Expr → List Statement → Statement
  | aliasstmt : List Alias → List Statement → Statement
  | proccall : ID → List Expr → Statement
  | clearstmt : Designator → Statement
  | errorstmt : String → Statement
  | assertstmt : Expr → String → Statement
  | putstmtexp : Expr → Statement
  | putstmtstr : String → Statement
  | returnstmt : Option Expr → Statement
  | undefine : ID → Statement
  deriving Inhabited

inductive Alias
  | mk : ID → Expr → Alias
  deriving Inhabited

inductive Rule
  | simplerule : Option String → Option Expr → List Decl → List Statement → Rule
  | startstate : Option String → List Decl → List Statement → Rule
  | invariant : Option String → Expr → Rule
  | ruleset : List Quantifier → List Rule → Rule
  | aliasrule : List Alias → List Rule → Rule
  deriving Inhabited

end -- mutual

structure Program where
  constdecls : List Decl
  typedecls : List Decl
  vardecls : List Decl
  procdecls  : List ProcDecl
  rules   : List Rule

def Designator.cons : Designator → (ID ⊕ Expr) → Designator
  | .mk id rest, new => Designator.mk id (rest ++ [new])

def Expr.appendCallArg : Expr → Expr → Expr
  | .call id args, newArg => .call id (args ++ [newArg])
  | expr, _ => expr

mutual

partial def Expr.beq : Expr → Expr → Bool
  | .designator d₁, .designator d₂ => d₁.beq d₂
  | .integerConst n₁, .integerConst n₂ => n₁ == n₂
  | .call id₁ exprs₁, .call id₂ exprs₂ =>
      id₁ == id₂ && exprs₁.length == exprs₂.length &&
      (exprs₁.zip exprs₂).foldl (init := true)
        λ res (e₁, e₂) => res && e₁.beq e₂
  | .universal q₁ e₁, .universal q₂ e₂ => q₁.beq q₂ && e₁.beq e₂
  | .existential q₁ e₁, .existential q₂ e₂ => q₁.beq q₂ && e₁.beq e₂
  | .binop op₁ e₁₁ e₁₂, .binop op₂ e₂₁ e₂₂ => op₁ == op₂ && e₁₁.beq e₂₁ && e₁₂.beq e₂₂
  | .negation e₁, .negation e₂ => e₁.beq e₂
  | .conditional c₁ t₁ e₁, .conditional c₂ t₂ e₂ => c₁.beq c₂ && t₁.beq t₂ && e₁.beq e₂
  | _, _ => false

partial def Quantifier.beq : Quantifier → Quantifier → Bool
  | .simple id₁ te₁, .simple id₂ te₂ => id₁ == id₂ && te₁.beq te₂
  | .assign id₁ e₁₁ e₁₂ oe₁, .assign id₂ e₂₁ e₂₂ oe₂ =>
    id₁ == id₂ && e₁₁.beq e₂₁ && e₁₂.beq e₂₂ &&
    match oe₁, oe₂ with
      | none, none => true
      | some exp₁, some exp₂ => Expr.beq exp₁ exp₂
      | _, _ => false
  | _, _ => false

partial def Designator.beq : Designator → Designator → Bool
  | .mk id₁ rest₁, .mk id₂ rest₂ => and (id₁ == id₂) $
    rest₁.zip rest₂ |>.map (λ (sum₁,sum₂) => match sum₁, sum₂ with
    | .inl id'₁, .inl id'₂ => id'₁ == id'₂
    | .inr exp₁, .inr exp₂ => Expr.beq exp₁ exp₂
    | _, _ => false)
      |>.all id

partial def TypeExpr.beq : TypeExpr → TypeExpr → Bool
  | .previouslyDefined id₁, .previouslyDefined id₂ => id₁ == id₂
  | .integerSubrange e₁ te₁, .integerSubrange e₂ te₂ => e₁.beq e₂ && te₁.beq te₂
  | .enum ids₁, .enum ids₂ => ids₁ == ids₂
  | .record decls₁, .record decls₂ => decls₁.zip decls₂ |>.all λ (d₁, d₂) => d₁.beq d₂
  | .array te₁₁ te₁₂, .array te₂₁ te₂₂ => te₁₁.beq te₂₁ && te₁₂.beq te₂₂
  | _, _ => false

partial def Decl.beq : Decl → Decl → Bool
  | .const id₁ e₁, .const id₂ e₂ => id₁ == id₂ && e₁.beq e₂
  | .type id₁ te₁, .type id₂ te₂ => id₁ == id₂ && te₁.beq te₂
  | .var  ids₁ te₁, .var ids₂ te₂ => ids₁ == ids₂ && te₁.beq te₂
  | _, _ => false

end

instance : BEq Designator where beq := Designator.beq
instance : BEq Decl where beq := Decl.beq
instance : BEq Expr where beq := Expr.beq
instance : BEq Quantifier where beq := Quantifier.beq
instance : BEq TypeExpr where beq := TypeExpr.beq

end Murϕ
