--> 26

interface Function T U { apply : T -> U };
map T U (f : Function T U) (a : [T]) : [U] =
  letrec go (i : Int) (acc : [U]) : [U] =
    if i == #a then acc else go (i + 1) (acc ++ [f.apply (a !! i)])
  in go 0 [];

interface Predicate T extends Function T Bool => {};
filter T (p : Predicate T) (a : [T]) : [T] =
  letrec go (i : Int) (acc : [T]) : [T] =
    if i == #a then acc else go (i + 1) (acc ++ if p.apply (a !! i) then [a !! i] else [])
  in go 0 [];

double = new trait implements Function Int Int => { apply = \(x : Int) -> x * 2; };
isEven = new trait implements Predicate Int => { apply = \(x : Int) -> x % 2 == 0; };

sum (a : [Int]) =
  letrec sum' (i : Int) : Int =
    if i == #a then 0 else a!!i + sum' (i+1)
  in sum' 0;
array = [1;2;3;4];
sum (map @Int @Int double array) + sum (filter @Int isEven array)