{
open Parser
}

let variable = ['A' - 'Z']+ ['A' - 'Z' '0' - '9']*
let white_space = [' ' '\t' '\r' '\n']

rule read = parse
	| white_space   { read lexbuf }
        | variable as v { VAR(v) }
        | "|-"          { PROOF }
        | ","           { COMMA }
        | "->"          { IMPL }
        | "&"           { AND }
        | "|"           { OR }
        | "!"           { NOT }
        | "("           { OPEN }
        | ")"           { CLOSE }
        | eof           { EOF }