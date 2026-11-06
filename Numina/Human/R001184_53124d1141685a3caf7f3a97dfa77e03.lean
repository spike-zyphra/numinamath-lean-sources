import Mathlib

/-A sequence $(a_n)$ is defined as follows:
\[a_{i + 1} = \frac{1}{1 - a_i}\]for $i \ge 1.$  If $a_3 = a_1,$ compute $(a_9)^9.$-/
theorem algebra_20945 {a : ℕ → ℝ} (ha : ∀ i, a (i + 1) = 1 / (1 - a i)) (ha0 : a 1 ≠ 0) (ha1 : a 1 ≠ 1) (ha2 : a 3 = a 1) :
    (a 9) ^ 9 = -1 := by
  -- set f to simplify the hypothesis
  set f := fun (x : ℝ) => 1 / (1 - x) with hf
  replace ha : ∀ i, a (i + 1) = f (a i) := by rw [hf]; simp at ha ⊢; exact ha
  -- show that a 1 = f (f (a 1))
  have h1 : a 1 = f (f (a 1)) := by 
    rw [<-ha 1, <-ha 2]
    norm_num
    exact ha2.symm
  -- show that ∀n, a (2 * n + 1) = a 1 (by induction)
  have hn1 : ∀ n, a (2 * n + 1) = a 1 := by
    intro n
    induction n with
    -- when n = 0, obviously
    | zero => norm_num
    -- when n satisfied, show the case of n + 1
    | succ n hn =>
      calc
        a (2 * (n + 1) + 1) = f (a (2 * (n + 1))) := by rw [ha]
        _ = f (a (2 * n + 1 + 1)) := by congr
        _ = f (f (a (2 * n + 1))) := by rw [ha]
        _ = f (f (a 1)) := by rw [hn]
        _ = a 1 := by rw [<-h1]
  -- sepecially, a 9 = a 1
  have h9 := hn1 4
  simp at h9
  -- so we just need to show that a 1 ^ 9 = -1
  rw [h9]
  clear hn1 h9
  -- show that 1 - a 1 ≠ 0, so that we can use field_simp
  replace ha1 : 1 - a 1 ≠ 0 := by
    intro h
    replace h : a 1 = 1 := by 
      calc 
        a 1 = 1 - (1 - a 1) := by ring_nf
        _ = 1 - 0 := by rw [h]
        _ = 1 := by norm_num
    rw [h] at ha1
    contradiction
  -- show that 1 - 1 / (1 - a 1) ≠ 0
  have ha3 : 1 - 1 / (1 - a 1) ≠ 0 := by
    field_simp
    exact ha0
  -- show that a 1 ≠ 0
  have ha4 : -a 1 ≠ 0 := by 
    contrapose! ha0
    calc
      a 1 = -(-a 1) := by ring_nf
      _ = -0 := by rw [ha0]
      _ = 0 := by norm_num
  -- so we can use field_simp to simplify a 1 = f (f (a 1)) to a 1 ^ 2 - a 1 + 1
  rw [hf] at h1
  field_simp at h1
  replace h1 : (a 1) ^ 2 - a 1 + 1 = 0 := by
    calc (a 1) ^ 2 - a 1 + 1
        = (a 1) ^ 2 + (1 - a 1) := by ring_nf
      _ = (a 1) ^ 2 + -(a 1 * a 1) := by rw [h1]
      _ = 0 := by ring_nf
  -- show that a 1 ^ 3 + 1 = 0
  replace h1 : a 1 ^ 3 + 1 = 0 := by
    calc a 1 ^ 3 + 1
        = (a 1 + 1) * (a 1 ^ 2 - a 1 + 1) := by ring_nf
      _ = (a 1 + 1) * 0 := by rw [h1]
      _ = 0 := by norm_num
  -- finally get the answer
  calc a 1 ^ 9
      = (a 1 ^ 3) ^ 3 := by ring_nf
    _ = (a 1 ^ 3 + 1 - 1) ^ 3 := by ring_nf
    _ = (-1) ^ 3 := by rw [h1]; ring_nf
    _ = -1 := by norm_num