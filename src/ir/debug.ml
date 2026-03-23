let level = ref 0

let msg component lvl fmt =
  Format.ksprintf
    (fun s -> if !level >= lvl then Printf.eprintf "[%s] %s\n%!" component s)
    fmt
