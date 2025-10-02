saveBetti = method()
saveBetti(List, String, String) := () => (B, filename, pwd) -> (
    (pwd | filename) << toExternalString(B) << close;
)
saveBetti(List,  String) := () => (B, filename) -> (
    pwd := currentDirectory() | "cache/";
    saveBetti(B, filename, pwd);
)

loadBetti = method()
loadBetti(String, String) := List => (filename, pwd) -> (
    value get (pwd | filename)
)
loadBetti(String) := List => filename -> (
    pwd := currentDirectory() | "cache/";
    loadBetti(filename, pwd)
)
