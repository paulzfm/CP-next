--> 4

interface A { foo : Int };
interface B { foo : Int };
a = new trait implements A => { foo = 1 };
b = new trait implements B => { foo = 2 };
getFoo (x : { foo : Int }) = x.foo;
getFooA (x : A) = x.foo;
getFoo a + getFoo b + getFooA a
-- + getFooA b -- error