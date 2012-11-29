
val n = CommandLine.name()
val () =
    case CommandLine.arguments() of
      [f] => AplCompile.compileAndRunFile f
    | _ => print ("Usage: " ^ n ^ " file.apl\n")
