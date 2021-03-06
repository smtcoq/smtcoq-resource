
VERNAC COMMAND EXTEND Parse_certif_zchaff
| [ "Parse_certif_zchaff" 
    ident(dimacs) ident(trace) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.parse_certif dimacs trace fdimacs fproof
  ]
| [ "Zchaff_Checker" string(fdimacs) string(fproof) ] ->
  [
    Zchaff.checker fdimacs fproof
  ]
| [ "Zchaff_Theorem" ident(name) string(fdimacs) string(fproof) ] ->
  [
    Zchaff.theorem name fdimacs fproof
  ] 
END

VERNAC COMMAND EXTEND Parse_certif_trim
| [ "Parse_certif_trim"
   ident(dimacs) ident(trace) string(fdimacs) string(fproof) ] ->
  [
    Trim.parse_certif dimacs trace fdimacs fproof 
  ] 
| [ "Trim_Checker" string(fdimacs) string(fproof) ] ->
  [
    Trim.checker fdimacs fproof
  ]
END

VERNAC COMMAND EXTEND Trim_Theo
| [ "Trim_Theorem" ident(dimacs) ident(thname) string(fdimacs) string(fproof) ] ->
  [
    Trim.theorem dimacs thname fdimacs fproof
  ] 
| [ "Trim_dimacs" ident(dimacs) string(fdimacs) ] ->
  [
    Trim.dimacs dimacs fdimacs 
  ] 
END

VERNAC COMMAND EXTEND Parse_certif_verit
| [ "Parse_certif_verit"
    ident(t_i) ident(t_func) ident(t_atom) ident(t_form) ident(root) ident(used_roots) ident(trace) string(fsmt) string(fproof) ] ->
  [
    Verit.parse_certif t_i t_func t_atom t_form root used_roots trace fsmt fproof
  ]
| [ "Verit_Checker" string(fsmt) string(fproof) ] ->
  [
    Verit.checker fsmt fproof
  ]
| [ "Verit_Theorem" ident(name) string(fsmt) string(fproof) ] ->
  [
    Verit.theorem name fsmt fproof
  ]
END

TACTIC EXTEND zchaff
| [ "zchaff" ] -> [ Zchaff.tactic ]
END

TACTIC EXTEND verit
| [ "verit" ] -> [ Verit.tactic ]
END
