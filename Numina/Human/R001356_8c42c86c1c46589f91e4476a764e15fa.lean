import Mathlib

/- Let $\mathbb{Z}$ be the set of integers. Determine all functions $f: \mathbb{Z} \rightarrow \mathbb{Z}$ such that, for all integers $a$ and $b$,  $$ f(2 a)+2 f(b)=f(f(a+b)) $$  (South Africa) -/
theorem algebra_23686 (f : ℤ → ℤ) : (∀ a b : ℤ, f (2 * a) + 2 * f b = f (f (a + b))) ↔
    (∀ n : ℤ, f n = 0) ∨ (∃ K, ∀ n : ℤ, f n = 2 * n + K):= by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  . have h1 : ∀ n : ℤ, 2 * f (n + 1) = 2 * f n + (f 2 - f 0):= fun n ↦ by
      have g1 := h 0 (n + 1)
      have g2 := h 1 n
      simp only [mul_zero, zero_add, mul_one, add_comm 1 n] at g1 g2
      have := g1.trans g2.symm
      linarith
    have h2 : 2 ∣ f 2 - f 0 := by
      specialize h1 0
      simp only [zero_add] at h1
      exact ⟨f 1 - f 0, by linarith⟩
    obtain ⟨d, h2⟩ := h2
    rw [h2] at h1
    replace h1 : ∀ n : ℤ, f (n + 1) = f n + d := fun n ↦ by specialize h1 n; linarith
    replace h1 : ∀ n : ℤ, ∀ m : ℕ, f (n + m) = f n + m * d := fun n m ↦ by
      induction m with
      | zero => simp
      | succ m ih =>
        specialize h1 (n + m)
        rw [Nat.cast_add, Nat.cast_one, ← add_assoc, h1, ih, add_mul, one_mul, ← add_assoc]
    replace h1 : ∀ n : ℤ, f n = n * d + f 0 := fun n ↦ by
      if h : 0 ≤ n then 
      specialize h1 0 (n.natAbs)
      simpa [show |n| = n from abs_of_nonneg h, add_comm] using h1
      else
      specialize h1 n ((-n).natAbs)
      simpa [abs_of_neg (a := n) (by simp_all), add_neg_eq_iff_eq_add, add_comm] using h1.symm
    have h3 : d = 0 ∨ d = 2:= by
      have g1:= h 0 1
      have g2:= h 1 1
      simp only [mul_zero, zero_add, mul_one, Int.reduceAdd] at g1 g2
      rw [h1 (f 1), h1 1] at g1
      rw [h1 (f 2), h1 1, h1 2] at g2
      replace g2 : d * (d - 2) = 0:= by linarith
      simpa [sub_eq_zero] using Int.mul_eq_zero.1 g2
    obtain rfl | rfl := h3
    . simp only [mul_zero, zero_add] at h1
      simp only [h1, add_right_eq_self, mul_eq_zero, OfNat.ofNat_ne_zero, false_or, forall_const] at h
      exact Or.intro_left _ (fun n ↦ h1 n|>.trans h)
    . right
      exact ⟨f 0, fun n ↦ by simpa [mul_comm] using h1 n⟩
  . obtain h | ⟨K, h⟩ := h
    . simp [h]
    . exact fun a b ↦ by simp only [h]; linarith