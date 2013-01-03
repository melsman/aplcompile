
val n = CommandLine.name()

fun usage() =
    (print ("Usage: " ^ n ^ " [-o ofile] file.apl\n");
     OS.Process.exit OS.Process.success)

fun runargs [f] = AplCompile.compileAndRunFile f
  | runargs ("-o" :: ofile :: rest) =
    (AplCompile.outfile := SOME ofile;
     runargs rest)
  | runargs _ = usage ()

val () = runargs(CommandLine.arguments())
