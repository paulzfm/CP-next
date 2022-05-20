--> 9

interface A { foo : Int };
interface B { foo : Int };
aTrait = trait implements A => { foo = 1; bar = 2 };
a = new aTrait;
b = new trait implements B => { foo = 2 };
getFoo (x : { foo : Int }) = x.foo;
getFooA (x : A) = x.foo;

interface C { foo : Int; bar : Int; baz : String };
c = new trait implements C inherits aTrait => { baz = "baz" };
-- TODO: inferred type seems redundant

a.bar + getFoo a + getFoo b + getFooA a
-- + getFooA b -- error
+ c.foo + c.bar