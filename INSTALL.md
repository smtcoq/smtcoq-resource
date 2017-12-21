# Compilation
- Compile https://github.com/smtcoq/native-coq branch "resource"
- Add environment variable: LD_LIBRARY_PATH=/path/to/native-coq-resource/kernel/resource/
- Compile and install ssreflect: use the version distributed here (which is a fork of ssr-1.4 to compile with old native-coq)
- Copy the native files: cp  theory/NSsreflect*    ..../user-contrib/Ssreflect/
