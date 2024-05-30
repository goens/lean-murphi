import Murphi.AST

namespace Murϕ

def indent : Nat → String
  | Nat.zero => ""
  | Nat.succ n => "  " ++ indent n

mutual
private partial def typeExprToString : TypeExpr → String
  | .previouslyDefined id => s!"{id}"
  | .integerSubrange startexp endexp => exprToString startexp ++ " .. " ++ exprToString endexp
  | .enum ids => "enum {" ++ (", ".intercalate ids) ++ "}"
  | .record decls => "record\n" ++
    (String.join (( decls.map declToString ).map fun str => (String.join ["  ", str, ";\n"] ) )) -- (";\n".intercalate $ decls.map declToString)
    ++ "end"
  | .array ty₁ ty₂ => "array [" ++ typeExprToString ty₁ ++ "] of " ++ typeExprToString ty₂

private partial def declToString : Decl → String
  | .const id expr => s!"{id} : " ++ exprToString expr
  | .type  id typeexpr => s!"{id} : " ++ typeExprToString typeexpr
  | .var  ids typeexpr => (",".intercalate ids) ++ " : " ++ typeExprToString typeexpr


private partial def exprToString : Expr → String
  | .designator des => designatorToString des
  | .integerConst i => i.repr
  | .call id actuals => s!"{id}(" ++ ", ".intercalate (actuals.map exprToString) ++ ")"
  | .universal quant doexp => "forall " ++ quantifierToString quant ++ " do " ++ exprToString doexp ++ " endforall"
  | .existential quant doexp => "exists " ++ quantifierToString quant ++ " do " ++ exprToString doexp ++ " endexists"
  | .binop op lhs rhs => "(" ++ exprToString lhs ++ s!" {op} " ++ exprToString rhs ++ ")"
  | .negation exp => "!(" ++ exprToString exp ++ ")"
  | .conditional cond thenexp elseexp => exprToString cond ++ " ? " ++ exprToString thenexp ++ " : " ++ exprToString elseexp

private partial def formalToString : Formal → String
  | .mk var ids type => (if var then "var " else "") ++ ", ".intercalate ids ++ " : " ++ typeExprToString type

private partial def procDeclToString (inputProcDecl : ProcDecl) : String :=
  let indentationLevel : Nat := 1
  let recCall := statementToString (indentationLevel := indentationLevel + 1)
  match inputProcDecl with
  | .procedure id formals decls statements => s!"procedure {id} (" ++ "; ".intercalate (formals.map formalToString) ++ ");\n"
    ++ "\n".intercalate (decls.map declToString) ++ "begin\n" ++ ";\n".intercalate (statements.map recCall)
    ++ ";\n end;"
  | .function id formals type decls statements => s!"function {id} (\n  " ++ ";\n  ".intercalate (formals.map formalToString) ++ "\n)"
    ++ " : " ++ typeExprToString type ++ ";\n" ++
    -- Function Variables, Syntax: var <var_name> : <var_type> ;
    String.join (( decls.map declToString ).map fun str => String.join ["  var ", str, ";\n"] ) -- "\n".intercalate (decls.map declToString)
    ++ "begin\n"
    ++ String.join (( statements.map recCall ).map fun str => String.join [(indent indentationLevel), str, ";\n"] )
    -- ";\n".intercalate (statements.map statementToString)
    ++ "end"

private partial def designatorToString : Designator → String
  | .mk id idorexps =>
    let idOrExpToString : Sum ID Expr → String
      | .inl id => s!".{id}"
      | .inr expr => "[ " ++ exprToString expr ++ " ]"
    id ++ String.join (idorexps.map idOrExpToString)

private partial def quantifierToString : Quantifier → String
  | .simple id type => s!"{id} : {typeExprToString type}"
  | .assign id exp toexp byexpOp =>
    let expS := exprToString exp
    let toexpS := exprToString toexp
    let byexpS := match byexpOp with
      | none => ""
      | some byexp => "by " ++ exprToString byexp
    s!"{id} := {expS} to {toexpS} {byexpS}"

private partial def statementToString ( indentationLevel := 0) (inputStatement : Statement)  : String :=
  let end_indents : String := indent (indentationLevel - 1)
  let recCall := statementToString (indentationLevel := indentationLevel + 1)
  match inputStatement with
  | .assignment des expr => (designatorToString des) ++ " := " ++ (exprToString expr)
  | .ifstmt cond thenstmts eliflist elsestmts =>
    let thenS := String.join (( thenstmts.map recCall ).map fun str => String.join [(indent indentationLevel), str, ";\n"] ) --";\n".intercalate $ thenstmts.map recCall
    let elseS :=
     if elsestmts.length == 0 then ""
     else end_indents ++ "else\n" ++
     String.join (( elsestmts.map recCall ).map fun str => String.join [(indent indentationLevel), str, ";\n"] ) -- ";\n".intercalate (elsestmts.map recCall)
    let elifS := String.intercalate " " $ eliflist.map λ (elifexp, elifstmts) =>
      s!"{end_indents}elsif {exprToString elifexp} then\n"
      ++ String.join (( elifstmts.map recCall ).map fun str => String.join [(indent indentationLevel), str, ";\n"] ) -- ";\n".intercalate (elifstmts.map recCall)
    s!"if {exprToString cond} then\n" ++ thenS ++ elifS ++ elseS ++ end_indents ++ "end"
  | .switchstmt exp cases elsestmts =>
    let casesS := "\n".intercalate $ cases.map
      λ (exps,stmts) => ",".intercalate (exps.map exprToString) ++ " : "
        ++ ";\n".intercalate (stmts.map recCall)
    let elseS := if elsestmts.length == 0 then ""
        else "else " ++ ";\n".intercalate (elsestmts.map recCall)
    s!"switch {exprToString exp}{casesS}{elseS}" ++ end_indents ++ "endswitch"
  | .forstmt quant stmts =>
    let stmtsS := (String.join (( stmts.map recCall ).map (fun str => String.join [(indent indentationLevel), str, ";\n"]) )) -- ";\n".intercalate (stmts.map recCall)
    s!"for {quantifierToString quant} do\n{stmtsS}" ++ end_indents ++ "endfor"
  | .whilestmt cond stmts =>
    let stmtsS := (String.join (( stmts.map recCall ).map (fun str => String.join [(indent indentationLevel), str, ";\n"]) )) -- ";\n".intercalate (stmts.map recCall)
    s!"while {exprToString cond} do\n{stmtsS}" ++ end_indents ++ "end"
  | .aliasstmt aliases stmts =>
    let stmtsS := (String.join (( stmts.map recCall ).map (fun str => String.join [(indent indentationLevel), str, ";\n"]) )) -- ";\n".intercalate (stmts.map recCall)
    "alias " ++ ("; ".intercalate $ aliases.map aliasToString) ++ s!" do\n{stmtsS}" ++ end_indents ++ "end"
  | .proccall id args => s!"{id} (" ++ (", ".intercalate $ args.map exprToString) ++ ")"
  | .clearstmt des => s!"clear {designatorToString des}"
  | .errorstmt msg => s!"error \"{msg}\""
  | .assertstmt exp msg => s!"assert {exprToString exp} \"{msg}\""
  | .putstmtexp exp => s!"put {exprToString exp}"
  | .putstmtstr str => s!"put {str}"
  | .returnstmt opExp => "return " ++ (match opExp with | none => "" | some exp => exprToString exp)
  | .undefine id => s!"undefine {id}"

private partial def aliasToString : Alias → String
  | .mk id exp => s!"{id} : {exprToString exp}"

private partial def ruleToString (inputRule : Rule) : String :=
  let indentationLevel : Nat := 1
  let recCall := statementToString (indentationLevel := indentationLevel + 1)
  match inputRule with
  | .simplerule opName opExp decls stmts =>
    let stmtsS := String.join (( stmts.map recCall ).map fun str => String.join [(indent ( indentationLevel )), str, ";\n"] ) -- ";\n".intercalate (stmts.map statementToString)
    let declsS := (String.join (( decls.map declToString ).map (fun str => String.join ["  var ", str, ";\n"]) )) -- String.intercalate ";\n" $ decls.map declToString
    let nameS := match opName with
      | none => ""
      | some name => name
    let expS := match opExp with
      | none => ""
      | some exp => exprToString exp ++ "\n==>\n"
      s!"rule \"{nameS}\" \n{expS} \n{declsS}\nbegin\n{stmtsS}\nend"
  | .startstate opName decls stmts =>
    let stmtsS := (String.join (( stmts.map recCall ).map (fun str => String.join ["  ", str, ";\n"]) )) -- ";\n".intercalate (stmts.map statementToString)
    let declsS := (String.join (( decls.map declToString ).map (fun str => String.join ["  var ", str, ";\n"]) )) -- String.intercalate ";\n" $ decls.map declToString
    let nameS := match opName with
      | none => ""
      | some name => name
    s!"startstate \"{nameS}\"{declsS}\nbegin\n{stmtsS} end"
  | .invariant opName exp =>
    let nameS := match opName with
      | none => ""
      | some name => name
    s!"invariant \"{nameS}\"\n{exprToString exp}"
  | .ruleset quants rules =>
    let quantsS := "; ".intercalate (quants.map quantifierToString)
    let rulesS := (String.join (( rules.map ruleToString ).map (fun str => String.join ["  ", str, ";\n"]) )) -- String.intercalate ";\n" $ rules.map ruleToString
    s!"\nruleset {quantsS} do \n{rulesS}end"
  | .aliasrule aliases rules =>
    let aliasesS := "; ".intercalate (aliases.map aliasToString)
    let rulesS := String.intercalate ";\n" $ rules.map ruleToString
    s!"alias {aliasesS} do {rulesS} end"
end


def Formal.toString : Formal → String := formalToString
instance : ToString Formal where toString := Formal.toString

def ProcDecl.toString : ProcDecl → String := procDeclToString
instance : ToString ProcDecl where toString := ProcDecl.toString

def Designator.toString : Designator → String := designatorToString
instance : ToString Designator where toString := Designator.toString

def Quantifier.toString : Quantifier → String := quantifierToString
instance : ToString Quantifier where toString := Quantifier.toString

def Statement.toString : Statement → String := statementToString
instance : ToString Statement where toString := Statement.toString

def Alias.toString : Alias → String := aliasToString
instance : ToString Alias where toString := Alias.toString

def Rule.toString : Rule → String := ruleToString
instance : ToString Rule where toString := Rule.toString

def Expr.toString : Expr → String := exprToString
instance : ToString Expr where toString := Expr.toString

def TypeExpr.toString : TypeExpr → String := typeExprToString
instance : ToString TypeExpr where toString := TypeExpr.toString

def Decl.toString : Decl → String := declToString
instance : ToString Decl where toString := Decl.toString

def Program.toString : Program → String
  | prog =>
    let constdecls := String.join (( prog.constdecls.map Decl.toString ).map fun str => str.append ";\n") -- String.intercalate ";\n" $ prog.constdecls.map Decl.toString
    let vardecls := String.join (( prog.vardecls.map Decl.toString ).map fun str => str.append ";\n") -- String.intercalate ";\n" $ prog.vardecls.map Decl.toString
    let typedecls := String.join (( prog.typedecls.map Decl.toString ).map fun str => str.append ";\n") -- String.intercalate ";\n" $ prog.typedecls.map Decl.toString
    let decls := s!"const\n{constdecls}\ntype\n{typedecls}\nvar\n{vardecls}\n"
    let procdecls := String.join (( prog.procdecls.map ProcDecl.toString ).map fun str => str.append ";\n\n") -- String.intercalate ";\n" $ prog.procdecls.map ProcDecl.toString
    let rules := String.join (( prog.rules.map Rule.toString ).map fun str => str.append ";\n\n") -- String.intercalate ";\n" $ prog.rules.map Rule.toString
  s!"{decls}\n{procdecls}\n{rules}"
instance : ToString Program where toString := Program.toString
