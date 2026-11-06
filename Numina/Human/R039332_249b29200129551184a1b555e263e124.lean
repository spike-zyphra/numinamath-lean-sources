import Mathlib

/- Define a function on the positive integers recursively by f(1)=2, f(n)=f(n−1)+1 if n is even
and f(n)=f(n−2)+2 if n is odd and greater than 1. What is f(2017)?
(A) 2017
(B) 2018
(C) 4034
(D) 4035
(E) 4036 -/
theorem number_theory_97620 {f : ℕ → ℕ}
(hf1 : f 1 = 2)
(hfn : ∀ n, Even n → f n = f (n - 1) + 1)
(hfn' : ∀ n, Odd n → n > 1 → f n = f (n - 2) + 2) :
f 2017 = 2018 := by
  -- we'll show f n = n+1 by induction (for n>=1)
  have h : ∀ n, f (n+1) = n+2 := by
    intro n
    induction n using Nat.twoStepInduction
    case zero => simpa
    case one => simp; have t:= hfn 2 (by norm_num); simpa [t]
    case more n' hmn hn' =>
      have hevenodd := Nat.even_or_odd (n'+2+1)
      cases' hevenodd with heven hodd
      -- · rw [hfn (n'+1) heven, Nat.add_sub_assoc (by trivial), Nat.sub_self, add_zero, hn]
      · rw [hfn (n'+2+1) heven, Nat.add_sub_assoc (by trivial), Nat.sub_self, add_zero, hn'];
      · rw [hfn' (n'+2+1) hodd (by linarith), add_assoc, add_comm 2 1, ← add_assoc, Nat.add_sub_assoc (by trivial), Nat.sub_self, Nat.add_zero, hmn]

  -- now we can solve the problem
  exact h 2016