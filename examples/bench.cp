--> 7773

f (a:Int) (b:Int) (c:Int) (d:Int) (e:Int) : Int =
  if a == 0 then 1 else
    if b == 0 then f (a-1) a a a a + 1 else
      if c == 0 then f a (b-1) b b b + 1 else
        if d == 0 then f a b (c-1) c c + 1 else
          if e == 0 then f a b c (d-1) d + 1 else
            f a b c d (e-1) + 1;
g (n:Int) = f n n n n n;
g 10
