
val n = CommandLine.name()

fun usage() =
    (print ("Usage: " ^ n ^ " [-o ofile] [-c] file.apl\n  -o file : specify output file\n  -c : compile only (no evaluation)\n");
     OS.Process.exit OS.Process.success)

val eval_p = ref true
fun runargs [f] = AplCompile.compileAndRunFile (!eval_p) f
  | runargs ("-o" :: ofile :: rest) =
    (AplCompile.outfile := SOME ofile;
     runargs rest)
  | runargs ("-c" :: rest) = 
    (eval_p := false;
     runargs rest)
  | runargs _ = usage ()

val () = runargs(CommandLine.arguments())
