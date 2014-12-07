module Foo(P: sig end) = struct
    type t = A
end

module Bar = struct end

module X: sig type t = private Foo(Bar).t end = struct
    type t = Foo(Bar).t
end ;;
