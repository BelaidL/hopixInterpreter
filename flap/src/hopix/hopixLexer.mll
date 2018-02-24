{
  open Lexing
  open Error
  open Position
  open HopixParser

  let next_line_and f lexbuf  =
    Lexing.new_line lexbuf;
    f lexbuf

  let error lexbuf =
    error "during lexing" (lex_join lexbuf.lex_start_p lexbuf.lex_curr_p)

   let to_char_aux c = char_of_int (int_of_string (
			  (String.sub c 2 ((String.length c)-3) )))

   let to_char c =
    match String.get c 2 with
    | 't'-> '\t'
    | '\\'-> '\\'
    | 'n'-> '\n'
    | 'b'-> '\b'
    | 'r'-> '\r'
    | '\''-> '\''
    |_-> failwith "format non reconnu"
   
   let conv_to_char c = 
    let len = String.length c in
    match len with
    | 3 -> String.get c 1
    | 4 -> to_char c
    | 6 -> to_char_aux c
    | _ -> match (String.sub c 2 2) with
	 |"0b"|"0B"|"0o"|"0O"|"0x"|"0X"-> to_char_aux c
	 | _ -> failwith "format non reconnu"

}



let symbol = [ '+' '-' '*' '/' '<' '=' '>' '&' '|' '_' ]

let punct = symbol | [ '`' '~' '!' '?' '@' '$' '%' '^' '#' ',' '.' ':' ';' '{' '}' '(' ')' '[' ']' ' ']

let newline = ('\010' | '\013' | "\013\010")

let blank   = [' ' '\009' '\012']

let alpha = ['0'-'9' 'A'-'Z' 'a'-'z' ]

let alien_infix_id = '`' ['A'-'Z' 'a'-'z' '0'-'9' '+' '-' '*' '/' '<' '=' '>' '_']+ '`'

let alien_prefix_id = '`' ['A'-'Z' 'a'-'z' '0'-'9' '+' '-' '*' '/' '<' '=' '>' '_']+

let var_id = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_' ]* | alien_prefix_id

let constr_id = ['A'-'Z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']* | '_' ['A'-'Z' 'a'-'z' '0'-'9' '_']+

let type_con = ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let type_variable = '\'' ['a'-'z'] ['A'-'Z' 'a'-'z' '0'-'9' '_']*

let integer = ['0'-'9']+ |'0'['x''X']['0'-'9' 'a'-'f' 'A'-'F']+ | '0' ['B' 'b']['0'-'1']+ | '0' ['O' 'o']['0'-'7']+ 

let printable = alpha | punct

let bina = '\\' '0' ['B' 'b']['0'-'1']+

let octa = '\\' '0' ['O' 'o']['0'-'7']+

let hexa = '\\''0'['x' 'X']['0'-'9' 'a'-'f' 'A'-'F']['0'-'9' 'a'-'f' 'A'-'F']

let ascii_char =  '\\' ['0'-'1']['0'-'9']['0'-'9'] | '\\' '2' ['0'-'5']['0'-'5']

let atom = ascii_char | hexa | octa | bina | printable | "\\""\\" | "\\""'" | "\\""n" | "\\""t" | "\\""b" | "\\""r"

let char = "'" (atom | '"') "'"

let string = '"' (atom | "'" | "\\""\"")* '"'
 
rule token = parse
  (** Layout *)
  | newline         { next_line_and token lexbuf }
  | blank+          { token lexbuf               }
  | "{-"            { comment_block 0 lexbuf     }
  | "--"            { comment_line lexbuf        }
  


  (** Symbols *)
  | "="       { EQUAL 	    }
  | ":="      { CEQUAL      }


  (** Keywords *)
  | "val"           { VAL    }
  | "extern"        { EXTERN }
  | "type"          { TYPE   }
  | "fun"           { FUN    }
  | "ref"	    { REF    }
  | "and"           { AND    }
  | "while"	    { WHILE  }
  | "if"            { IF     }
  | "then"          { THEN   }
  | "elif"          { ELIF   }
  | "else"          { ELSE   }
  (** literal **)
  | integer as n                             { INT (Int32.of_string n)     }
  | char as c                                { CHAR (conv_to_char c)       }
  | string as s                              { eval "" (from_string (String.sub s 1 (String.length s - 2)))   }
  (** Identifiers **)
  | type_variable as i      { TYPEVAR  i  }
  | alien_infix_id as i     { INFIXID i   }	
  | var_id as i             { VARID    i  }
  | constr_id as i          { CONSTRID i  }
  

  (** Operators **)
  | "&&"      { ANDLOGIC     }
  | "||"      { ORLOGIC      }
  | "*"       { STAR         }
  | "+"       { PLUS         }
  | "-"       { MINUS        }
  | "/"       { SLASH        }
  | "<="      { LOWEREQUAL   }
  | ">="      { GREATEREQUAL }	
  | "<"       { LOWERTHAN    }
  | ">"       { GREATERTHAN  }
  | "\\"      { ANTISLASH    }

  (** Punctiation **)
  | ","       { COMMA        }
  | ":"       { COLON        }
  | ";"       { SEMICOLON    }
  | "->"      { LRARROW      }
  | "=>"      { ARROW        }
  | "_"	      { UNDERSCORE   }
  | "?"       { QUESTIONMARK }
  | "("       { LPAREN       }
  | ")"       { RPAREN       }
  | "["       { LBRACKET     }
  | "]"       { RBRACKET     }
  | "|"       { PIPE         }
  | "!"	      { EXCLPOINT    }
  | "&"       { AMPER        }
  | "{"       { LBRACE       }
  | "}"       { RBRACE       }
  


  | eof       { EOF          }

  (** Lexing error. *)
  | _               { error lexbuf "unexpected character." }


 and comment_block lvl = parse 
| "{-"    { comment_block (lvl + 1) lexbuf       }
| "-}"    { 
            if lvl = 0
            then  token lexbuf
            else comment_block (lvl - 1) lexbuf
                                            }
| _       { comment_block lvl lexbuf}
| eof     { error lexbuf "comment unclosed" }


 and comment_line = parse
| eof | newline    { token lexbuf        }
| _                { comment_line  lexbuf} 


and eval s =parse
| (atom|"'") as c     { eval (s^(String.make 1 (conv_to_char ("'"^c^"'") ))) lexbuf }
| '\\''"'             { eval ( s^"\"") lexbuf                                       }
| eof                 { STRING s                                                    }
