--> 0

interface A { f1 : Int };
interface B T { f2 : T };
interface C T { f3 : T };
interface D T U extends A, B T, C U => { f4 : U };
interface E T extends D T T => {};

fooA (x : A) = x.f1;
fooC T (x : C T) = x.f3;
d = new trait implements D String Int => {
  f1 = 1; f2 = "hello"; f3 = 3; f4 = 4
};
tr = trait => { f1 = -1; f2 = -2; f3 = -3; f4 = -4 };
e = new trait implements E Int inherits tr => {};
fooA d + fooC @Int d + fooA e + fooC @Int e