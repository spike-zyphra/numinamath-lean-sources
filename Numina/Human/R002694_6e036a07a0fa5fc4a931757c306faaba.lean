import Mathlib

/- # Problem:
 8. For a real number $x$, $[x]$ denotes the greatest integer not exceeding $x$. For some integer $k$, there are exactly 2008 positive integers $n_{1}, n_{2}, \cdots, n_{2008}$, such that $k=\left[\sqrt[3]{n_{1}}\right]=\left[\sqrt[3]{n_{2}}\right]=\cdots=\left[\sqrt[3]{n_{2008}}\right]$, and $k$ divides $n_{i}(i=$ $1,2, \cdots, 2008)$, then $k=$ $\qquad$
8. 668 详解: 若 $\sqrt[3]{n}-1n$, 满足 $k$ 整除 $n$, 则 $n$ 可取 $k^{3}, k^{3}+k, \cdots, k^{3}+3 k^{2}+3 k$,共 $3 k+4$ 个, 所以 $3 k+4=2008, k=668$. -/
theorem number_theory_101223 :
    {k : ℕ | 0 < k ∧ {n : ℕ | k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ ∧ k ∣ n}.encard = 2008} = {668} := by
  -- Show that for any k ∈ ℕ, {n : ℕ | k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ ∧ k ∣ n} = {k³, k³ + k, ..., k³ + 3k² + 3k}.
  suffices ∀ k : ℕ, 0 < k → {n : ℕ | k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ ∧ k ∣ n} = Finset.image (fun i => k ^ 3 + i * k) (Finset.range (3 * k + 4)) by
    -- Use the above result to show that the only k such that the cardinality is 2008 is k = 668.
    ext k
    by_cases hk : 0 < k
    . -- Deal with the normal case where k > 0.
      rw [Set.mem_setOf, this k hk, Set.encard_coe_eq_coe_finsetCard]
      -- Note that the mapping i => k³ + i * k is injective.
      rw [Finset.card_image_of_injective]
      simp [hk]
      norm_cast
      omega
      -- Verify that the mapping is injective.
      intro i j hij
      simp at hij
      omega
    . -- Deal with the case k = 0, which is not actually under our consideration.
      simp [hk]
      omega
  intro k hk
  ext n
  simp [-one_div]
  constructor
  . -- Given that k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋ and k ∣ n, show that n is of the form k³ + i * k for some i < 3k + 4.
    rintro ⟨h₀, h₂⟩
    symm at h₀
    rw [Int.floor_eq_iff] at h₀
    obtain ⟨h₀, h₁⟩ := h₀
    -- We have n ≥ k³.
    replace h₀ := pow_le_pow_left₀ (by positivity) h₀ 3
    nth_rw 2 [<-Real.rpow_natCast] at h₀
    rw [<-Real.rpow_mul (by simp)] at h₀
    simp at h₀
    norm_cast at h₀
    -- We have n < (k + 1) ^ 3.
    replace h₁ := pow_lt_pow_left₀ h₁ (by positivity) (show 3 ≠ 0 by norm_num)
    rw [<-Real.rpow_natCast, <-Real.rpow_mul (by simp)] at h₁
    simp at h₁
    norm_cast at h₁
    -- Let n = mk for some m.
    rw [dvd_iff_exists_eq_mul_left] at h₂
    obtain ⟨m, rfl⟩ := h₂
    -- We have k² ≤ m ≤ k² + 3k + 3.
    rw [show (k + 1) ^ 3 = (k ^ 2 + 3 * k + 3) * k + 1 by ring, Nat.lt_add_one_iff] at h₁
    rw [show k ^ 3 = k ^ 2 * k by ring] at h₀
    replace h₀ := Nat.le_of_mul_le_mul_right h₀ hk
    replace h₁ := Nat.le_of_mul_le_mul_right h₁ hk
    -- Write m = k² + x.
    obtain ⟨x, h₀⟩ := Nat.exists_eq_add_of_le h₀
    use x
    simp [h₀] at h₁ ⊢
    refine ⟨by omega, by ring⟩
  . -- Show that for x < 3k + 4, n = k³ + xk satisfies the condition.
    rintro ⟨x, h₀, h₁⟩
    refine ⟨?_, ?_⟩
    . -- First show that k = ⌊(n : ℝ) ^ ((1 : ℝ) / 3)⌋.
      symm
      rw [Int.floor_eq_iff]
      refine ⟨?_, ?_⟩
      . -- Show that k ≤ n ^ (1 / 3).
        apply le_of_pow_le_pow_left₀ (show 3 ≠ 0 by norm_num) (by positivity)
        nth_rw 2 [<-Real.rpow_natCast]
        rw [<-Real.rpow_mul (by simp)]
        simp
        norm_cast
        omega
      . -- Show that n ^ (1 / 3) < k + 1.
        apply lt_of_pow_lt_pow_left₀ 3 (by positivity)
        rw [<-Real.rpow_natCast, <-Real.rpow_mul (by simp)]
        simp
        norm_cast
        nlinarith
    . -- Show that k ∣ n.
      rw [<-h₁, pow_succ, <-add_mul]
      apply dvd_mul_left
