import Mathlib

/- Denote by $\mathbb{N}$ the positive integers. Let $f: \mathbb{N} \rightarrow \mathbb{N}$ be a function such that, for any $w, x, y, z \in \mathbb{N}$,

$$
f(f(f(z))) f(w x f(y f(z)))=z^{2} f(x f(y)) f(w)
$$

Show that $f(n!) \geq n$ ! for every positive integer $n$.-/
theorem number_theory_609572 (f : ℕ → ℕ) (hf : ∀ n ≥ 1, f n ≥ 1) (hf' : ∀ w x y z : ℕ, 1 ≤ w → 1 ≤ x → 1 ≤ y → 1 ≤ z → f (f (f z)) * (f (w * x * f (y * f z))) = z ^ 2 * f (x * f y) * f w) :
    ∀ n ≥ 1, f (n.factorial) ≥ n.factorial := by
  -- Some subtle lemma to guarantee that the value of f is positive.
  have g₀ : f 1 ≥ 1 := hf 1 (by rfl)
  have g₁ : f (f 1) ≥ 1 := hf (f 1) g₀
  -- Show that f is injective.
  have h₀ (z₁ z₂ : ℕ) (hz₁ : 1 ≤ z₁) (hz₂ : 1 ≤ z₂) (hz : f z₁ = f z₂): z₁ = z₂ := by
    -- Suppose f(z₁) = f(z₂).
    -- Substitute (1, 1, 1, z₁) and (1, 1, 1, z₂) into the original equation respectively.
    have h₀ := hf' 1 1 1 z₁ (by rfl) (by rfl) (by rfl) hz₁
    have h₁ := hf' 1 1 1 z₂ (by rfl) (by rfl) (by rfl) hz₂
    -- Compare the two equations.
    rw [<-hz] at h₁
    rw [h₁] at h₀
    simp [show f 1 ≠ 0 by linarith only [g₀], show f (f 1) ≠ 0 by linarith only [g₁]] at h₀
    exact h₀.symm
  -- Show that f(f(1)) ⬝ f(yf(1)) = f(y).
  have h₁ (y : ℕ) (hy : 1 ≤ y) : (f (f 1)) * f (y * f 1) = f y := by
    -- Substitute (f(f(1)), 1, y, 1) into the original equation.
    have h₁ := hf' (f (f 1)) 1 y 1 g₁ (by rfl) hy (by rfl)
    rw [mul_comm] at h₁
    simp [show f (f (f 1)) ≠ 0 by linarith only [hf (f (f 1)) g₁]] at h₁
    -- Apply injectivity of f.
    apply h₀ at h₁
    exact h₁
    -- Verify some statements of the form 1 ≤ (f(⬝)).
    . nth_rw 1 [show 1 = 1 * 1 by norm_num]
      apply mul_le_mul
      . exact g₁
      . apply hf
        nlinarith only [hy, g₀]
      . norm_num
      . simp
    . exact hf y hy
  -- We have f(y) = (f(f(1)))ⁿ ⬝ f(y⬝ f(1)ⁿ) for all n.
  have h₂ (y n : ℕ) (hy : 1 ≤ y) : f y = (f (f 1)) ^ n * f (y * f 1 ^ n) := by
    -- Perform induction on n.
    induction n with
    | zero =>
      simp
    | succ n hn =>
      have g : 1 ≤ y * f 1 ^ n := by
        nth_rw 1 [show 1 = 1 * 1 by norm_num]
        apply mul_le_mul
        . exact hy
        . apply Nat.one_le_pow
          linarith only [g₀]
        . norm_num
        . simp
      -- Substitute y = y (f(1))ⁿ into the previous equation.
      specialize h₁ (y * f 1 ^ n) g
      rw [mul_assoc, <-Nat.pow_succ] at h₁
      rw [Nat.pow_succ, mul_assoc, h₁]
      exact hn
  -- Note that f(f(1))ⁿ ≤ f(1) for all n.
  have h₃ (n : ℕ) : f (f 1) ^ n ≤ f 1 := by
    -- This is because f(f(1))ⁿ ∣ f(1) by the previous divisibility condition.
    apply Nat.le_of_dvd
    linarith only [g₀]
    specialize h₂ 1 n (by rfl)
    nth_rw 2 [h₂]
    apply Nat.dvd_mul_right
  -- Now we show that we must have f(f(1)) = 1.
  replace h₃ : 1 = f (f 1) := by
    by_contra this
    -- Otherwise, f(f(1)) > 1.
    replace this : f (f 1) > 1 := Nat.lt_of_le_of_ne g₁ this
    -- Now we can derive a contradiction.
    specialize h₃ (Nat.log (f (f 1)) (f 1 * f (f 1)))
    apply Nat.le_log_of_pow_le this at h₃
    rw [Nat.log_mul_base this (by linarith only [g₀])] at h₃
    omega
  -- We prove also that f(1) = 1.
  have h₄ : f 1 = 1 := by
    -- Substitute f(f(1)) into h₁.
    simp [<-h₃] at h₁
    specialize h₁ 1 (by rfl)
    -- Use injectivity of f.
    apply h₀ at h₁
    simp at h₁
    exact h₁
    linarith only [g₀]
    norm_num
  -- We have f(xy) = f(x)f(y).
  have h₅ (x y : ℕ) (hx : 1 ≤ x) (hy : 1 ≤ y) : f (x * y) = f x * f y := by
    -- Substitute (x, y, 1, 1) into the original equation.
    specialize hf' x y 1 1 hx hy (by rfl) (by rfl)
    simp [h₄] at hf'
    rw [hf']
    ac_rfl
  -- For each n, we have |{f(1), f(2), ..., f(n)}|= n.
  have h₆ (n : ℕ) (hn : 1 ≤ n) : (Finset.image f (Finset.Icc 1 n)).card = (Finset.Icc 1 n).card := by
    -- Since f is injective, the image of f on Icc 1 n has exactly n elements.
    apply Finset.card_image_of_injOn
    simp [Set.InjOn]
    intro k₀ hk₀ _ k₁ hk₁ _ hfk
    apply h₀
    assumption'
  simp at h₆
  have h₇ (n : ℕ) (S : Finset ℕ) (hS : ∀ i ∈ S, 1 ≤ i) (hS' : S.card = n) : ∏ i ∈ S, i ≥ n.factorial := by
    -- We show by induction on n that for any finite set S ⊆ ℕ⁺ with S.card = n, it's product is at least n!.
    revert S
    induction n with
    | zero =>
      -- We have S = ∅.
      intro S hS hS'
      rw [Finset.card_eq_zero] at hS'
      simp [hS']
    | succ n hn =>
      intro S hS hS'
      -- Since S is nonempty, let m be its maximum.
      obtain ⟨m, hm, hmax⟩ : ∃ m ∈ S, ∀ x ∈ S, ¬m < x := by
        apply Finset.exists_maximal
        rw [<-Finset.card_ne_zero, hS']
        simp
      -- Show that m ≥ n + 1.
      have hm' : m ≥ n + 1 := by
        -- Assume on the contrary that m < n + 1.
        by_contra! hm''
        -- Then every element of S is at most n.
        -- This contradicts the fact that S has n + 1 elements.
        have hS'' : S.card ≤ (Finset.Icc 1 n).card := by
          apply Finset.card_le_card
          intro x hx
          specialize hmax x hx
          specialize hS x hx
          simp at hmax ⊢
          omega
        rw [hS'] at hS''
        simp at hS''
      -- Remove the maximum element m from S.
      let S' := S.erase m
      -- Show that S' has cardinal n.
      have hS'' : S'.card = n := by
        rw [Finset.card_erase_of_mem hm, hS', Nat.add_sub_cancel]
      calc
        _ = m * ∏ x ∈ S.erase m, x := by rw [<-Finset.mul_prod_erase S _ hm]
        _ ≥ (n + 1) * n.factorial := by
          apply mul_le_mul
          . -- We have m ≥ n + 1 as proved above.
            exact hm'
          . -- We have n! ≤ ∏ x ∈ S.erase m, x by induction hypothesis.
            apply hn
            . intro i hi
              exact hS i (Finset.mem_of_mem_erase hi)
            . exact hS''
          . simp
          . simp
        _ = (n + 1).factorial := by
          rw [Nat.factorial_succ]
  -- Now we may conclude the goal.
  intro n hn
  calc
    _ = ∏ i ∈ Finset.Icc 1 n, f i := by
      -- By multiplicity of f, write f(n!) = f(1) ⬝ f(2) ⬝ ⋯ ⬝ f(n).
      rw [<-Finset.prod_Ico_id_eq_factorial]
      apply Nat.exists_eq_add_of_le' at hn
      obtain ⟨n, rfl⟩ := hn
      -- Perform induction on n.
      induction n with
      | zero =>
        simp
      | succ n hn =>
        -- Use the multiplicity of f.
        rw [Finset.prod_Ico_succ_top (by simp), h₅ _ _ (by simp; apply Nat.factorial_pos) (by simp), hn]
        symm
        rw [Finset.prod_Icc_succ_top (by simp)]
    _ = ∏ i ∈ (Finset.image f (Finset.Icc 1 n)), i := by
      -- It is equal to the product of the image of f on Icc 1 n.
      rw [Finset.prod_image]
      -- Verify that f is injective on Icc 1 n.
      intro x hx y hy hxy
      simp at hx hy
      exact h₀ x y hx.1 hy.1 hxy
    _ ≥ n.factorial := by
      -- By the previous lemma, we have ∏ i ∈ (Finset.image f (Finset.Icc 1 n)), i ≥ n!.
      apply h₇
      . intro i hi
        simp at hi
        obtain ⟨j, hj⟩ := hi
        rw [<-hj.2]
        exact hf j hj.1.1
      . exact h₆ n hn
