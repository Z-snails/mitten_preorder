type t = Lexing.position * Lexing.position

type 'a with_loc = { data: 'a; loc: t }
