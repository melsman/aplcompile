structure AplToMla = AplCompile(Mla)
structure AplToC = AplCompile(ILapl)

val name = CommandLine.name()

fun usage() =
    (print ("Usage: " ^ name ^ " [-o ofile] [-c] [-v] [-ml] file.apl\n" ^
            "   -o file : specify output file\n" ^
            "   -c : compile only (no evaluation)\n" ^
            "   -ml : use ML backend\n" ^
            "   -v : verbose\n");
     OS.Process.exit OS.Process.success)

val compileAndRunFile = ref AplToC.compileAndRunFile

fun runargs args flags =
    case args of
        [f] => !compileAndRunFile flags f
      | "-ml" :: rest => compileAndRunFile := AplToMla.compileAndRunFile
                         before runargs rest flags
      | "-o" :: ofile :: rest => runargs rest (("-o",SOME ofile)::flags)
      | f :: rest =>  runargs rest ((f,NONE)::flags)
      | _ => usage ()

val () = runargs (CommandLine.arguments()) nil
