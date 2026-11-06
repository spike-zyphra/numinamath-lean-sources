import Mathlib

/-A sequence of positive integers $a_{1}, a_{2}, a_{3}, \ldots$ satisfies

$$
a_{n+1}=n\left\lfloor\frac{a_{n}}{n}\right\rfloor+1
$$

for all positive integers $n$. If $a_{30}=30$, how many possible values can $a_{1}$ take? (For a real number $x$, $\lfloor x\rfloor$ denotes the largest integer that is not greater than $x$.)-/

def c_val_helper (i : ℕ) : ℕ :=
    match i with
    | 0 => 1
    | Nat.succ i' => 
    let c_next := c_val_helper i' 
    (c_next + Rat.ceil (Rat.div c_next (29 - i))).toNat

def c_val (i : ℕ ) : ℕ := 
  c_val_helper (29 - i)
  
theorem combinatorics_610202 : c_val 1 = 274 := by
  native_decide