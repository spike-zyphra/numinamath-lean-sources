import Mathlib

/-Let $C$ be the circle with equation $x^2-6y-3=-y^2-4x$. If $(a,b)$ is the center of $C$ and $r$ is its radius, what is the value of $a+b+r$?-/
theorem number_theory_608030 {a : ℕ → ℤ} (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 2016)
  (h1 : ∀ i j : ℕ, (i : ℤ) + j ∣ (i * a i + j * a j)) : ∀ i, 0 < i → i ≤ 2016 → a i = a 2016 := by
    have l1 : ∀ i j : ℕ, |a i - a j| < 2017 := by
      intro i j
      have := ha i
      have := ha j
      rw [abs_sub_lt_iff]
      omega
    -- The condition rewrites to $i+j \mid i\left(a_{i}-a_{j}\right)$
    have h2 : ∀ i j : ℕ, (i : ℤ) + j ∣ i * (a i - a j) := by
      intro i j
      convert Int.dvd_sub (h1 i j) (dvd_mul_right ((i : ℤ) + j) (a j)) using 1
      linarith
    --  Since $2 k-1$ and $k$ are coprime, we see that $2 k-1 \mid a_{k}-a_{k-1}$. Thus if $2 k-1&gt;2016$, then $a_{k}=a_{k-1}$. 
    have h3 : ∀ k, 1009 ≤ k → a k = a (k - 1) := by
      intro k hk
      have h3 : IsCoprime (2*k - 1 : ℤ) k := by
        suffices IsCoprime (k - 1 : ℤ) k by
          convert (IsCoprime.add_mul_left_left_iff (z := 1)).2 this using 1
          linarith
        exact ⟨-1, 1, by linarith⟩
      specialize h2 k (k - 1)
      norm_cast at h2
      have h4 : (2*k - 1 : ℤ) ∣ a k - a (k - 1) := by
        rw [←Nat.add_sub_assoc (by omega), ←two_mul, Nat.cast_sub (by omega)] at h2
        exact IsCoprime.dvd_of_dvd_mul_left h3 h2
      have h5 : |a k - a (k - 1)| < (2*k - 1 : ℤ) := (l1 k (k-1)).trans_le (by linarith)
      exact sub_eq_zero.1 <| Int.eq_zero_of_abs_lt_dvd h4 h5
    -- since $a_{k}$ and $a_{k-1}$ are non-negative and at most 2016. All together $a_{1009}=a_{1010}=\cdots=a_{2016}$.
    replace h3 : ∀ k, 1009 ≤ k → a k = a 2016 := by
      have l1 : ∀ k, 1009 ≤ k → a k = a 1009 := by
        intro k hk
        induction' k, hk using Nat.le_induction with k hk ind
        · rfl
        · exact (h3 (k + 1) (by omega)).trans ind
      intro k hk
      have := l1 k hk
      have := l1 2016 (by omega)
      linarith
    intro i ipos hi
    -- for any $i < 1009$, let $j = 2017 - i$.
    let j := 2017 - i
    by_cases i1009 : i < 1009
    · -- when i < 1009, 1009 ≤ j. We can get 2017 ∣ a i - a j from h2, but a i - a j < 2017, so a i = a j = a 2016.
      have hj : 1009 ≤ j := by omega
      specialize h2 i j
      have hij : i + j = 2017 := by omega
      simp [←Nat.cast_add, hij] at h2
      have p2017 : Prime (2017 : ℤ) := by rw [Int.prime_iff_natAbs_prime]; native_decide

      have cop2017i : IsCoprime (2017 : ℤ) i := (Prime.coprime_iff_not_dvd p2017).2
        (fun dvdi => by linarith [Int.le_of_dvd (by positivity) dvdi])
      have h4 := IsCoprime.dvd_of_dvd_mul_left cop2017i h2
      have h5 := Int.eq_zero_of_abs_lt_dvd h4 (l1 i j)
      rw [sub_eq_zero.1 h5, h3 j hj]
    · -- when 1009 ≤ i, a i = a 2016 because of h3.
      simp at i1009
      exact h3 i i1009
