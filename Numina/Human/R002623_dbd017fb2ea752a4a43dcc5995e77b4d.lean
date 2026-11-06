import Mathlib

/- A function f is defined recursively by f(1) = f(2) = 1 and f(n) = f(n - 1) - f(n - 2) + n
for all integers n ≥ 3. What is f(2018)?
(A) 2016
(B) 2017
(C) 2018
(D) 2019
(E) 2020 -/
theorem algebra_96975 {f : ℕ → ℤ} (hf1 : f 1 = 1) (hf2 : f 2 = 1)
(hfn : ∀ n ≥ 3, f n = f (n - 1) - f (n - 2) + n) :
f 2018 = 2017 := by
  -- let's calculate first 6 terms
  have h3 : f 3 = f 2 - f 1 + 3 := hfn 3 (by norm_num); rw [hf2, hf1] at h3; norm_num at h3;
  have h4 : f 4 = f 3 - f 2 + 4 := hfn 4 (by norm_num); rw [h3, hf2] at h4; norm_num at h4;
  have h5 : f 5 = f 4 - f 3 + 5 := hfn 5 (by norm_num); rw [h4, h3] at h5; norm_num at h5;
  have h6 : f 6 = f 5 - f 4 + 6 := hfn 6 (by norm_num); rw [h5, h4] at h6; norm_num at h6;
  -- now we show that ∀ n≥7 f n = f (n-6) + 6
  have han7: ∀ n≥7, f n = f (n-6) + 6 := by
    intro n hn
    calc f n
    _ = f (n-1) - f (n-2) + n := by rw [hfn n (by linarith)]
    _ = (f (n-2) - f (n-3) + n - 1) - f (n-2) + n := by rw [hfn (n-1) (by linarith [Nat.sub_le_sub_right hn 1])]; simp [Nat.sub_sub]; rw [← add_sub]; norm_num; exact Nat.cast_sub (by linarith)
    _ = -f (n-3) + 2*n - 1 := by ring_nf
    _ = -(f (n-4) - f (n-5) + n-3) + 2*n - 1 := by rw [hfn (n-3) (by linarith [Nat.sub_le_sub_right hn 3])]; simp [Nat.sub_sub]; rw [add_sub, ← sub_sub, ← sub_add, Nat.cast_sub (by linarith)]; simp; ring_nf;
    _ = -(f (n-4)) + f (n-5) + n + 2 := by ring_nf
    _ = -(f (n-5) - f (n-6) + n-4) + f (n-5) + n + 2 := by rw [hfn (n-4) (by linarith [Nat.sub_le_sub_right hn 4])]; simp [Nat.sub_sub]; rw[Nat.cast_sub (by linarith)]; simp; ring_nf
    _ = f (n-6) + 6 := by ring_nf

  -- now let's show this for larger offsets
  have han7': ∀ n k, n≥ 1 → f (n+6*k) = f n + 6*k := by
    intro n k hn
    induction k with
    | zero => simp
    | succ k ih => {
      specialize han7 (n+6*(k+1)) (by linarith)
      rw [han7, mul_add, Nat.add_sub_assoc (by linarith), mul_one, Nat.add_sub_cancel, ih, Nat.cast_add, mul_add, add_assoc]
      simp
    }
  -- now we can calculate f 2018
  calc f 2018
  _ = f (2 + 6*336) := by norm_num
  _ = f 2 + 6*336 := by rw [han7' 2 336 (by norm_num)]; simp
  _ = 2017 := by rw [hf2]; norm_num