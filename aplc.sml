structure AplToMla = AplCompile(Mla)
structure AplToC = AplCompile(ILapl)

val name = CommandLine.name()

fun usage() =
    (print ("Usage: " ^ name ^ " [-o ofile] [-c] [-v] [-ml] file.apl...\n" ^
            "   -o file : specify output file\n" ^
            "   -c : compile only (no evaluation)\n" ^
            "   -noopt : disable optimizations\n" ^
            "   -ml : use ML backend\n" ^
            "   -v : verbose\n");
     OS.Process.exit OS.Process.success)

val compileAndRunFiles = ref AplToC.compileAndRunFiles

fun isFlag s =
    case String.explode s of
        #"-" :: _ => true
      | _ => false

fun runargs args flags =
    case args of
        "-ml" :: rest => compileAndRunFiles := AplToMla.compileAndRunFiles
                         before runargs rest flags
      | "-o" :: ofile :: rest => runargs rest (("-o",SOME ofile)::flags)
      | f :: rest => 
        if isFlag f then runargs rest ((f,NONE)::flags)
        else !compileAndRunFiles flags args
      | nil => usage ()

val () = runargs (CommandLine.arguments()) nil
