def do_twice (f : ℕ → ℕ) (x : ℕ) : ℕ := f (f x) 
#check do_twice 
#print do_twice 

def curry 