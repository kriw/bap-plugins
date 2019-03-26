let id x = x
let () = Bap.Std.Project.register_pass ~deps:["myssa"; "copypropagation"; "mydeadcode"] id
