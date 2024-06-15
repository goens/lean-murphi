import Lean
import Murphi.Util
import Murphi.AST
import Murphi.Pretty

open Lean Syntax
namespace Murϕ

declare_syntax_cat formal
declare_syntax_cat proc_decl
declare_syntax_cat designator
declare_syntax_cat quantifier
declare_syntax_cat mur_statement
declare_syntax_cat statements
declare_syntax_cat mur_alias
declare_syntax_cat mur_rule
declare_syntax_cat mur_expr
declare_syntax_cat type_expr
declare_syntax_cat decl
declare_syntax_cat var_decls
declare_syntax_cat const_decls
declare_syntax_cat type_decls
declare_syntax_cat var_decl
declare_syntax_cat const_decl
declare_syntax_cat type_decl
declare_syntax_cat program
declare_syntax_cat paramident
declare_syntax_cat paramstr
declare_syntax_cat justparam

syntax (name := paramident1) ident : paramident
syntax (name := paramident2) "£" ident : paramident
syntax (name := paramident3) "£(" ident ")" : paramident

syntax (name := paramstr1) str : paramstr
syntax (name := paramstr2) "£" ident : paramstr

syntax (name := justparam1) "£" ident : justparam
syntax (name := justparam2) "£(" ident ")" : justparam

syntax "var" paramident,+ ":" type_expr : formal
syntax  paramident,+ ":" type_expr : formal
syntax "procedure" paramident "(" sepBy(formal,";") ")" ";" (var_decls* "begin")* mur_statement* patternIgnore("end" <|> "endprocedure") : proc_decl
syntax "function" paramident "(" sepBy(formal,";",";",allowTrailingSep) ")" ":" type_expr ";" (var_decls* "begin")? (statements)? patternIgnore("end" <|> "endfunction") : proc_decl

syntax paramident : designator
syntax designator "." paramident : designator
syntax designator "[" mur_expr "]" : designator
syntax (name := simplequantifier) paramident ":" type_expr : quantifier
syntax (name := quantifierassign) paramident ":=" mur_expr "to" mur_expr ("by" mur_expr)? : quantifier
syntax designator ":=" mur_expr : mur_statement
syntax "if" mur_expr "then" statements
       ("elsif" mur_expr "then" statements)*
       ("else" sepBy(mur_statement,";",";",allowTrailingSep))? patternIgnore("endif" <|> "end") : mur_statement
syntax "switch" mur_expr ("case" mur_expr,+ ":" mur_statement*)* ("else" mur_statement*)? ("end" <|> "endswitch") : mur_statement
syntax "for" quantifier "do" sepBy(mur_statement,";","; ",allowTrailingSep) patternIgnore("end" <|> "endfor") : mur_statement
syntax "while" mur_expr "do" sepBy(mur_statement,";",";",allowTrailingSep) patternIgnore("end" <|> "endwhile") : mur_statement
syntax "alias" sepBy(mur_alias,";",";",allowTrailingSep) "do" statements patternIgnore("end" <|> "endalias") : mur_statement
syntax paramident "(" mur_expr,+ ")" : mur_statement
syntax "clear" designator : mur_statement
syntax "error" str : mur_statement
syntax "assert" mur_expr (str)? : mur_statement
syntax "put" (mur_expr <|> str) : mur_statement
syntax "return" (mur_expr)? : mur_statement
syntax "undefine" ident : mur_statement
syntax justparam : statements
syntax mur_statement ";" : statements
syntax justparam ";" : statements
syntax mur_statement ";" statements : statements
syntax justparam ";" statements : statements
syntax paramident ":" mur_expr : mur_alias
syntax "rule" (paramstr)? (mur_expr "==>")? (var_decls* "begin")? statements patternIgnore("end" <|> "endrule") : mur_rule
-- commenting this out with the above removes the errors on individual statements, which makes no sense to me
-- syntax  "rule" (str)? (expr "==>")? (decl* "begin")? statement* "end" : mur_rule
syntax  "startstate" (str)? (var_decls* "begin")? statements patternIgnore("end" <|> "endstartstate") : mur_rule
syntax "invariant" (str)? mur_expr : mur_rule
syntax "ruleset" sepBy1(quantifier,";") "do" sepBy(mur_rule,";",";",allowTrailingSep) patternIgnore("end" <|> "endruleset") : mur_rule -- TODO: see if we need to add (";")?
syntax "alias" sepBy1(mur_alias,";") "do" sepBy(mur_rule,";") patternIgnore("end" <|> "endalias"): mur_rule
syntax justparam : mur_expr
syntax "(" mur_expr ")" : mur_expr
syntax designator : mur_expr
syntax num : mur_expr
syntax paramident "(" mur_expr,* ")" : mur_expr -- still don't know what "actuals" are
syntax "forall" quantifier "do" mur_expr patternIgnore("end" <|> "endforall") : mur_expr
syntax "exists" quantifier "do" mur_expr patternIgnore("end" <|> "endexists") : mur_expr
syntax mur_expr "+" mur_expr : mur_expr
syntax mur_expr "-" mur_expr : mur_expr
syntax mur_expr "*" mur_expr : mur_expr
syntax mur_expr "/" mur_expr : mur_expr
syntax mur_expr "%" mur_expr : mur_expr
syntax mur_expr "|" mur_expr : mur_expr
syntax mur_expr "&" mur_expr : mur_expr
syntax mur_expr "->" mur_expr : mur_expr
syntax mur_expr "<" mur_expr : mur_expr
syntax mur_expr "<=" mur_expr : mur_expr
syntax mur_expr ">" mur_expr : mur_expr
syntax mur_expr ">=" mur_expr : mur_expr
syntax mur_expr "=" mur_expr : mur_expr
syntax mur_expr "!=" mur_expr : mur_expr
syntax "!" mur_expr : mur_expr
syntax mur_expr "?" mur_expr ":" mur_expr : mur_expr
syntax paramident : type_expr
syntax mur_expr ".." mur_expr : type_expr
syntax "enum" "{" paramident,+ "}" : type_expr
syntax "record" sepBy(var_decl,";",";",allowTrailingSep) patternIgnore("endrecord" <|> "end") : type_expr
syntax "array" "[" type_expr "]" "of" type_expr : type_expr
syntax (name := vardecl) paramident,+ ":" type_expr : var_decl
syntax (name := constdecl) paramident ":" mur_expr : const_decl
syntax (name := typedecl) paramident ":" type_expr : type_decl
syntax "const" sepBy(const_decl,";",";",allowTrailingSep) : const_decls
syntax "type" sepBy(type_decl,";",";",allowTrailingSep) : type_decls
syntax "var" sepBy(var_decl,";",";",allowTrailingSep) : var_decls
syntax (name := constdeclp) justparam : const_decl
syntax (name := vardeclp) justparam : var_decl
syntax (name := typedeclp) justparam : type_decl
syntax justparam : decl
syntax justparam : proc_decl
syntax justparam : mur_rule
syntax const_decls type_decls var_decls sepBy(proc_decl,";",";",allowTrailingSep) sepBy(mur_rule,";",";",allowTrailingSep) : program

syntax "[murϕ|" proc_decl "]" : term
syntax "[murϕ|" designator "]" : term
syntax "[murϕ|" quantifier "]" : term
syntax "[murϕ|" mur_statement "]" : term
syntax "[murϕ|" statements "]" : term
syntax "[murϕ|" mur_alias "]" : term
syntax "[murϕ|" mur_rule "]" : term
syntax "[murϕ|" mur_expr "]" : term
syntax "[murϕ|" type_expr "]" : term
syntax "[murϕ|" var_decls "]" : term
syntax "[murϕ|" const_decls "]" : term
syntax "[murϕ|" type_decls "]" : term
syntax "[murϕ|" decl "]" : term
syntax "[murϕ_program|" program "]" : term
syntax "[murϕ_formal|" formal "]" : term
syntax "[murϕ_proc_decl|" proc_decl "]" : term
syntax "[murϕ_designator|" designator "]" : term
syntax "[murϕ_quantifier|" quantifier "]" : term
syntax "[murϕ_statement|" mur_statement "]" : term
syntax "[murϕ_statements|" statements "]" : term
syntax "[murϕ_alias|" mur_alias "]" : term
syntax "[murϕ_rule|" mur_rule "]" : term
syntax "[murϕ_expr|" mur_expr "]" : term
syntax "[murϕ_type_expr|" type_expr "]" : term
syntax "[murϕ_decl|" decl "]" : term
syntax "[murϕ_var_decl|" var_decl "]" : term
syntax "[murϕ_var_decls|" var_decls "]" : term
syntax "[murϕ_type_decls|" type_decls "]" : term
syntax "[murϕ_const_decls|" const_decls "]" : term

macro_rules
  | `([murϕ| $x:proc_decl  ]) => `(proc_decl| $x)
  | `([murϕ| $x:quantifier ]) => `(quantifier| $x)
  | `([murϕ| $x:statements ]) => `(statements| $x)
  | `([murϕ| $x:mur_statement  ]) => `(mur_statement| $x)
  | `([murϕ| $x:mur_alias  ]) => `(mur_alias| $x)
  | `([murϕ| $x:mur_rule   ]) => `(mur_rule| $x)
  | `([murϕ| $x:mur_expr       ]) => `(mur_expr| $x)
  | `([murϕ| $x:type_expr  ]) => `(type_expr| $x)
  | `([murϕ| $x:decl       ]) => `(decl| $x)
  | `([murϕ| $x:var_decls]) => `(var_decls| $x)
  | `([murϕ| $x:const_decls]) => `(const_decls| $x)
  | `([murϕ| $x:type_decls]) => `(type_decls| $x)
 -- | `([murϕ| $x:designator]) => `(designator| $x)
  | `([murϕ_formal| $x:formal]) => `(formal| $x)
  | `([murϕ_proc_decl| $x:proc_decl]) => `(proc_decl| $x)
  | `([murϕ_quantifier| $x:quantifier]) => `(quantifier| $x)
  | `([murϕ_statement| $x:mur_statement]) => `(mur_statement| $x)
  | `([murϕ_statements| $x:statements]) => `(statements| $x)
  | `([murϕ_alias| $x:mur_alias]) => `(mur_alias| $x)
  | `([murϕ_rule| $x:mur_rule]) => `(mur_rule| $x)
  | `([murϕ_expr| $x:mur_expr]) => `(mur_expr| $x)
  | `([murϕ_type_expr| $x:type_expr]) => `(type_expr| $x)
  | `([murϕ_decl| $x:decl]) => `(decl| $x)
  | `([murϕ_var_decl| $x:var_decl]) => `(var_decl| $x)
  | `([murϕ_designator| $x:designator]) => `(designator| $x)
  | `([murϕ_program| $x:program    ]) => `(program| $x)
  | `([murϕ_var_decls| $x:var_decls]) => `(var_decls| $x)
  | `([murϕ_const_decls| $x:const_decls]) => `(const_decls| $x)
  | `([murϕ_type_decls| $x:type_decls]) => `(type_decls| $x)


abbrev TMacro α := TSyntax α → MacroM Term

private def foldlSyntaxArrayJoinAux
  {α : SyntaxNodeKinds}
  (expandFun : TSyntax α → MacroM Term)
  (rest : Term)
  (val : TSyntax α) : MacroM Term := do
  `($rest ++ $(← expandFun val))

def foldlSyntaxArrayJoin {α : SyntaxNodeKinds} :
TSyntaxArray α → (TSyntax α → MacroM Term) → MacroM Term
  | es, expandFun => do
    let folded : Term ← es.foldlM (foldlSyntaxArrayJoinAux expandFun) (← `([]))
    return Lean.quote folded

def mapSyntaxArray {α : SyntaxNodeKinds} :
TSyntaxArray α → (TSyntax α → MacroM Term) → MacroM Term
  | es, expandFun => do
    let esArr : Array Term ← es.mapM expandFun
    return Lean.quote esArr.toList

-- HACK!
-- def expandTMacros {α} : TSyntax α → MacroM Term
--   | t => do return ⟨← Lean.expandMacros t⟩

def expandJustParam : TMacro `justparam
|  `(justparam| £ $x:ident ) => `($x)
|  `(justparam| £($x:ident) ) => `($x)
| _ => Lean.Macro.throwUnsupported

@[macro paramident1]
def expandJustParamMacro1 : Macro
  | `(justparam| $p) => expandJustParam p

@[macro paramident2]
def expandJustParamMacro2 : Macro
  | `(justparam| $p) => expandJustParam p

def expandParamIdent : TMacro `paramident
  |  `(paramident| $x:ident) => `($(Lean.quote x.getId.toString))
  |  `(paramident| £ $x:ident ) => `($x)
  |  `(paramident| £($x:ident) ) => `($x)
  | _ => Lean.Macro.throwUnsupported

-- This feels very hacky! But it won't work with <|>. TODO: I should produce an MWE
@[macro paramident1]
def expandParamIdentMacro1 : Macro
  | `(paramident| $p) => expandParamIdent p

@[macro paramident2]
def expandParamIdentMacro2 : Macro
  | `(paramident| $p) => expandParamIdent p

@[macro paramident3]
def expandParamIdentMacro3 : Macro
  | `(paramident| $p) => expandParamIdent p

def expandParamStr : TMacro `paramstr
  |  `(paramstr| $x:str) => `($x)
  |  `(paramstr| £ $x:ident ) => `($x)
  | _ => Lean.Macro.throwUnsupported

@[macro paramstr1]
def expandParamStrMacro1 : Macro
  | `(paramstr| $p) => expandParamStr p

@[macro paramstr2]
def expandParamStrMacro2 : Macro
  | `(paramstr| $p) => expandParamStr p

def expandVarDecl : TMacro `var_decl
  | `(var_decl| $[$ids:paramident],* : $t:type_expr ) => do
    let idsList : Term ← mapSyntaxArray ids expandParamIdent
    `([Decl.var $idsList [murϕ_type_expr| $t]])
  | `(var_decl| $p:justparam) => do `($(← expandJustParam p))
  | _ => Lean.Macro.throwUnsupported

-- Hack to lift expandVarDecl to the untyped macro world
@[macro vardecl]
def expandVarDeclMacro : Macro
 | `(var_decl| $v) => expandVarDecl v

@[macro vardeclp]
def expandVarDeclPMacro : Macro
 | `(var_decl| $v) => expandVarDecl v

-- syntax paramident ":" expr : const_decl
def expandTypeDecl : TMacro `type_decl
  | `(type_decl| $id:paramident : $t:type_expr ) => do
    `([Decl.type $(← expandParamIdent id) [murϕ_type_expr| $t]])
  | `(type_decl| $p:justparam) => do `($(← expandJustParam p))
  | _ => Lean.Macro.throwUnsupported


@[macro typedeclp]
def expandTypeDeclPMacro : Macro
 | `(type_decl| $d:type_decl) => expandTypeDecl d

@[macro typedecl]
def expandTypeDeclMacro : Macro
 | `(type_decl| $d:type_decl) => expandTypeDecl d

def expandConstDecl : TMacro `const_decl
  | `(const_decl| $id:paramident : $e:mur_expr ) => do
    `([Decl.const $(← expandParamIdent id) [murϕ_expr| $e]])
  | `(const_decl| $p:justparam) => do `($(← expandJustParam p))
  | _ => Lean.Macro.throwUnsupported

@[macro constdecl]
def expandConstDeclMacro : Macro
  | `(const_decl| $d) => expandConstDecl d

@[macro constdeclp]
def expandConstDeclPMacro : Macro
  | `(const_decl| $d) => expandConstDecl d

def expandSimpleQuantifier : TMacro `quantifier
  | `(quantifier| $x:paramident : $t) => do
   `(Quantifier.simple $(← expandParamIdent x) [murϕ_type_expr| $t])
  | _ => Lean.Macro.throwUnsupported

@[macro simplequantifier]
def  expandSimpleQuantifierMacro : Lean.Macro
  | `(quantifier| $v) => expandSimpleQuantifier v

@[macro quantifierassign]
def expandQuantifierAssign : Lean.Macro
  | `(quantifier| $x:paramident := $e₁ to $e₂ $[by $e₃]?) => do
    let x' <- expandParamIdent x
    -- TODO: deal with e₃
    `(Quantifier.assign $x' [murϕ_expr| $e₁] [murϕ_expr| $e₂] none)
  | _ => Lean.Macro.throwUnsupported

--def expandQuantifier := expandSimpleQuantifier >=> expandQuantifierAssign

macro_rules
  | `(var_decls| var $[$vardecls];*) => do
   foldlSyntaxArrayJoin vardecls expandVarDecl
  | `(type_decls| type $[$typedecls];*) => do
   foldlSyntaxArrayJoin typedecls expandTypeDecl
  | `(const_decls| const $[$constdecls];*) => do
   foldlSyntaxArrayJoin constdecls expandConstDecl
  | `(decl| $p:justparam) => do `($(← expandJustParam p))

macro_rules
  | `(type_expr| $x:paramident) => do `(TypeExpr.previouslyDefined $(← expandParamIdent x))
  | `(type_expr| $x:mur_expr .. $y) => do `(TypeExpr.integerSubrange [murϕ_expr| $x] [murϕ_expr| $y])
  | `(type_expr| enum { $[$ids],*} ) => do `(TypeExpr.enum $(← mapSyntaxArray ids expandParamIdent))
  | `(type_expr| record $[$decls];* end ) => do `(TypeExpr.record $(← foldlSyntaxArrayJoin decls λ d => `([murϕ_var_decl| $d]) ) )
  | `(type_expr| array[$t₁] of $t₂) => do `(TypeExpr.array [murϕ_type_expr| $t₁] [murϕ_type_expr| $t₂])


macro_rules
  | `(mur_rule| rule $(x)? $e ==> $(vds)* begin $stmts end) => do
    let xSyn <- match x with
      | none => `(none)
      | some x' =>
        let expanded <- expandParamStr x'
        `(some $expanded)
    let dsSyn ← mapSyntaxArray vds λ d => `([murϕ_var_decls| $d])
    `([Rule.simplerule $xSyn [murϕ_expr| $e] (List.join $dsSyn) [murϕ_statements| $stmts]])
  | `(mur_rule| ruleset $[$quantifiers];* do $[$rules];* endruleset ) => do
    let qs <- mapSyntaxArray quantifiers λ q => `([murϕ_quantifier| $q])
    let rs <- foldlSyntaxArrayJoin rules λ r => `([murϕ_rule| $r])
    `([Rule.ruleset $qs $rs])
  | `(mur_rule| invariant $[$s]? $e) => match s with
    | none => `(Rule.invariant none [murϕ_expr| $e])
    | some str => `([Rule.invariant (some $str) [murϕ_expr| $e]])
  | `(mur_rule| startstate $[$name]? $[$decls]* begin $stmts end) => do
    let dsSyn ← mapSyntaxArray decls λ d => `([murϕ_var_decls| $d])
    let nameSyn ← match name with
      | none => `(none)
      | some str => `(some $str)
     `([Rule.startstate $nameSyn $dsSyn [murϕ_statements| $stmts]])
  | `(mur_rule| startstate $[$name:str]? $stmts:statements end) => do
    let nameSyn ← match name with
      | none => `(none)
      | some str => `(some $str)
    `([Rule.startstate $nameSyn [] [murϕ_statements| $stmts]])
  | `(mur_rule| $p:justparam) => do `($(← expandJustParam p))

syntax  "startstate" (str)? (decl "begin")? statements ("end" <|> "endstartstate") : mur_rule

macro_rules
  | `(statements| $stmt:justparam ;) => do `( [ $(← expandJustParam stmt) ])
  | `(statements| $stmts:justparam ) => do `( $(← expandJustParam stmts))
  | `(statements| $stmt:mur_statement ;) => `( [ [murϕ_statement| $stmt] ])
  | `(statements| $stmt:justparam ; $stmts:statements) => do `( $(← expandJustParam stmt) ++ [murϕ_statements| $stmts])
  | `(statements| $stmt:mur_statement ; $stmts:statements) => `([murϕ_statement| $stmt] :: [murϕ_statements| $stmts])

macro_rules
  | `(mur_expr| $p:justparam) => do do `( $(← expandJustParam p))
  | `(mur_expr| $x + $y) => `(Murϕ.Expr.binop "+" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x - $y) => `(Murϕ.Expr.binop "-" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x * $y) => `(Murϕ.Expr.binop "*" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x / $y) => `(Murϕ.Expr.binop "/" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x % $y) => `(Murϕ.Expr.binop "%" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x | $y) => `(Murϕ.Expr.binop "|" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x & $y) => `(Murϕ.Expr.binop "&" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x -> $y) => `(Murϕ.Expr.binop "->" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x < $y) => `(Murϕ.Expr.binop "<" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x <= $y) => `(Murϕ.Expr.binop "<=" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x > $y) => `(Murϕ.Expr.binop ">" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x >= $y) => `(Murϕ.Expr.binop ">=" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x = $y) => `(Murϕ.Expr.binop "=" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| $x != $y) => `(Murϕ.Expr.binop "!=" [murϕ_expr| $x] [murϕ_expr| $y])
  | `(mur_expr| !$x) => `(Murϕ.Expr.negation [murϕ_expr| $x])
  | `(mur_expr| ($e:mur_expr)) => `([murϕ_expr| $e])
  | `(mur_expr| $x:designator ) => `(Murϕ.Expr.designator [murϕ_designator| $x])
  | `(mur_expr| $x:num ) => `(Murϕ.Expr.integerConst $x)
  | `(mur_expr| $x:paramident($es:mur_expr,*) ) => do
    let args <- mapSyntaxArray es.getElems λ e => `([murϕ_expr|$e])
    `(Murϕ.Expr.call $(← expandParamIdent x) $args)
--  syntax paramident "(" expr,* ")" : expr -- still don't know what "actuals" are

macro_rules
  | `(designator| $x:ident ) => do
    let ids := x.getId.components
    let mkCons := fun nm : Name => `(Sum.inl $(quote nm.toString))
    match ids with
      | [] => panic "Error, parsed identifier with 0 components. This should not happen"
      | name::names => do
        let namesStxList ← names.mapM mkCons --  `($(quote <| names.mapM mkCons))
        `(Designator.mk $(quote name.toString) $(quote namesStxList))
  | `(designator| $x:paramident ) => do `(Designator.mk $(← expandParamIdent x) [])
  | `(designator| $d:designator [$e:mur_expr] ) => `(Designator.cons [murϕ_designator| $d] $ Sum.inr [murϕ_expr| $e])
  | `(designator| $d:designator.$x:paramident ) => do `(Designator.cons [murϕ_designator| $d] $ Sum.inl $(← expandParamIdent x))

macro_rules
  | `(mur_statement| $x:designator := $y ) => `(Statement.assignment [murϕ_designator| $x] [murϕ_expr| $y])
  | `(mur_statement| for $q do $[$stmts];* endfor) => do
  let stmtsSyntax ← mapSyntaxArray stmts λ s => `([murϕ_statement| $s])
  `(Statement.forstmt [murϕ_quantifier| $q] $stmtsSyntax)
  | `(mur_statement| while $expr do $[$stmts];* endwhile) => do
  let stmtsSyntax ← mapSyntaxArray stmts λ s => `([murϕ_statement| $s])
  `(Statement.whilestmt [murϕ_expr| $expr] $stmtsSyntax)
  | `(mur_statement| if $e then $thens:statements $[elsif $es then $elsifs:statements]* $[else $[$opElses];*]? endif) => do
  let thensSyntax ← `([murϕ_statements| $thens])
  let elseifsSyntax ← es.toList.zip elsifs.toList |>.mapM λ (exp, stmts) => `(([murϕ_expr| $exp],[murϕ_statements| $stmts]))
  let elses := match opElses with
    | none => #[]
    | some es => es
  let elsesSyntax ← mapSyntaxArray elses λ s => `([murϕ_statement| $s])
  `(Statement.ifstmt [murϕ_expr| $e] $thensSyntax $(Lean.quote elseifsSyntax) $elsesSyntax)
  | `(mur_statement| assert $e $[$s]?) =>
  let strSyn := match s with
    | some strSyn => strSyn
    | none => Lean.quote ""
  `(Statement.assertstmt [murϕ_expr| $e] $strSyn)
  | `(mur_statement| error $msg) => `(Statement.errorstmt $msg)
  | `(mur_statement| return $[$exp]?) => match exp with | none => `(Statement.returnstmt none) | some e => `(Statement.returnstmt (some [murϕ_expr| $e]))
  | `(mur_statement| undefine $id ) => `(Statement.undefine $(quote id.getId.toString))
  | `(mur_statement| alias $[$aliases];* do $stmts endalias) => do
    let aliasesSyn ← mapSyntaxArray aliases λ a => `([murϕ_alias| $a ])
    `(Statement.aliasstmt $aliasesSyn [murϕ_statements| $stmts])

macro_rules
  | `(formal| var $[$pis],* : $te) => do
    let ids ← mapSyntaxArray pis expandParamIdent
    `(Formal.mk true $(ids) [murϕ_type_expr| $te])
  | `(formal| $[$pis],* : $te) => do
    let ids ← mapSyntaxArray pis expandParamIdent
    `(Formal.mk false $(ids) [murϕ_type_expr| $te])

macro_rules
  | `(proc_decl| function $pi ($[$formals:formal];*) : $te; $[$decls:var_decls]* begin $[$opStmts:statements]? end) => do
    let formalsSyn ← mapSyntaxArray formals λ f => `([murϕ_formal| $f])
    let declsArray : Array Term ← decls.mapM λ d => `([murϕ_var_decls| $d])
    let declsSyn : Term ← `(List.join $(Lean.quote declsArray.toList))
    let stmts ← match opStmts with | none => `([]) | some ss => `([murϕ_statements| $ss])
    `([ProcDecl.function $(← expandParamIdent pi) $formalsSyn [murϕ_type_expr| $te] $declsSyn $stmts])
  | `(proc_decl| function $pi ($[$formals:formal];*) : $te;  $[$opStmts:statements]? end) => do
    let formalsSyn ← mapSyntaxArray formals λ f => `([murϕ_formal| $f])
    let stmts ← match opStmts with | none => `([]) | some ss => `([murϕ_statements| $ss])
    `([ProcDecl.function $(← expandParamIdent pi) $formalsSyn [murϕ_type_expr| $te] [] $stmts])
  | `(proc_decl| $p:justparam) => do `($(← expandJustParam p))

macro_rules
  | `(mur_alias|  $pi:paramident : $expr ) => do `(Alias.mk $(← expandParamIdent pi) [murϕ_expr| $expr])

macro_rules
  | `(program|  $cdecls:const_decls $tdecls:type_decls $vdecls:var_decls $[$procdecls];* $[$rules];*) => do
    let procdeclsSyn ← foldlSyntaxArrayJoin procdecls λ d => `([murϕ_proc_decl| $d])
    let rulesSyn ← foldlSyntaxArrayJoin rules λ r => `([murϕ_rule| $r])
    `({ vardecls := [murϕ_var_decls| $vdecls], typedecls := [murϕ_type_decls| $tdecls],
        constdecls := [murϕ_const_decls| $cdecls],
        procdecls := $procdeclsSyn, rules := $rulesSyn : Program})

end Murϕ
