
module Make : functor(O:LexUtils.Config) -> sig
  val token : Lexing.lexbuf -> JavaParser.token
end