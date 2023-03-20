namespace Lurk.DSL

declare_syntax_cat    atom_
scoped syntax "t"   : atom_
scoped syntax "T"   : atom_
scoped syntax "nil" : atom_
scoped syntax "NIL" : atom_

declare_syntax_cat       op₁
scoped syntax "atom"   : op₁
scoped syntax "ATOM"   : op₁
scoped syntax "car"    : op₁
scoped syntax "CAR"    : op₁
scoped syntax "cdr"    : op₁
scoped syntax "CDR"    : op₁
scoped syntax "emit"   : op₁
scoped syntax "EMIT"   : op₁
scoped syntax "commit" : op₁
scoped syntax "COMMIT" : op₁
scoped syntax "comm"   : op₁
scoped syntax "COMM"   : op₁
scoped syntax "open"   : op₁
scoped syntax "OPEN"   : op₁
scoped syntax "num"    : op₁
scoped syntax "NUM"    : op₁
scoped syntax "u64"    : op₁
scoped syntax "U64"    : op₁
scoped syntax "char"   : op₁
scoped syntax "CHAR"   : op₁

declare_syntax_cat        op₂
scoped syntax "cons"    : op₂
scoped syntax "CONS"    : op₂
scoped syntax "strcons" : op₂
scoped syntax "STRCONS" : op₂
scoped syntax "+"       : op₂
scoped syntax "-"       : op₂
scoped syntax "*"       : op₂
scoped syntax "/"       : op₂
scoped syntax "%"       : op₂
scoped syntax "="       : op₂
scoped syntax "<"       : op₂
scoped syntax ">"       : op₂
scoped syntax "<="      : op₂
scoped syntax ">="      : op₂
scoped syntax "eq"      : op₂
scoped syntax "EQ"      : op₂
scoped syntax "hide"    : op₂
scoped syntax "HIDE"    : op₂

end Lurk.DSL