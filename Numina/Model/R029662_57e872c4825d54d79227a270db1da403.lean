import Mathlib

open Nat Real

lemma lemma_1 {n : ℕ} (hn : 0 < n) (x : ℝ) (hx : 0 < x) :
    ∏ i ∈ Finset.Icc 1 n, (x + i) > n ! := by
  have h2 : n ≥ 1 := by linarith
  have h4 : ∏ i in Finset.Icc 1 n, (i : ℝ) < ∏ i in Finset.Icc 1 n, (x + (i : ℝ) : ℝ) := by
    apply Finset.prod_lt_prod
    ·
      intro i hi
      have h6 : (i : ℝ) ≥ (1 : ℝ) := by
        have h10 : i ≥ 1 := by
          have h8 : i ∈ Finset.Icc 1 n := by
            exact hi
          simp at h8 ⊢
          all_goals omega
        have h11 : (i : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h10
        linarith
      linarith [h6]
    ·
      intro i hi
      have h41 : (i : ℝ) > 0 := by
        have h10 : i ≥ 1 := by
          have h8 : i ∈ Finset.Icc 1 n := by
            exact hi
          simp at h8 ⊢
          all_goals omega
        have h11 : (i : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h10
        linarith
      linarith [h41]
    ·
      use 1
      constructor
      ·
        have h17 : (1 : ℕ) ∈ Finset.Icc 1 n := by
          simp at *
          all_goals omega
        exact h17
      ·
        have h41 : (1 : ℝ) < (x + (1 : ℝ) : ℝ) := by
          have h9 : 0 < x := hx
          linarith
        simpa using h41
  have h10 : ∏ i in Finset.Icc 1 n, (i : ℝ) = (n ! : ℝ) := by
    have h11 : ∀ n : ℕ, ∏ i in Finset.Icc 1 n, (i : ℝ) = (n ! : ℝ) := by
      intro n
      induction n with
      | zero =>
        simp
      | succ n ih =>
        rw [Finset.prod_Icc_succ_top (by omega)]
        rw [ih]
        simp [Nat.factorial]
        all_goals norm_num
        all_goals ring
    specialize h11 n
    simpa using h11
  rw [h10] at h4
  exact h4

theorem algebra_225264 {n : ℕ} (hn : 0 < n) (x : ℝ)
    (hx : x > 0) (h : ∏ i ∈ Finset.range (n + 1), (x + i) = 1) :
    x < 1 / Nat.factorial n := by
  have eq1 : ∏ i ∈ Finset.range (n + 1), (x + i) = x * ∏ i in Finset.Icc 1 n, (x + i : ℝ) := by
    have eq2 : ∏ i ∈ Finset.range (n + 1), (x + i : ℝ) =
        (∏ i in Finset.range 1, (x + (i : ℝ) : ℝ)) * (∏ i in Finset.Icc 1 n, (x + (i : ℝ) : ℝ)) := by
      rw [show Finset.range (n + 1) = Finset.range 1 ∪ Finset.Icc 1 n by
        ext i
        simp
        omega
      ]
      rw [Finset.prod_union (by
        simp
      )]
    have eq6 : ∏ i in Finset.range 1, (x + (i : ℝ) : ℝ) = (x : ℝ) := by
      norm_num
    rw [eq6] at eq2
    simpa using eq2
  rw [eq1] at h

  have h12 : ∏ i in Finset.Icc 1 n, (x + (i : ℝ) : ℝ) > (n ! : ℝ) := by
    apply lemma_1 hn x hx

  have h14 : (x : ℝ) * (↑(n !) : ℝ) < (1 : ℝ) := by
    have h15 : (∏ i in Finset.Icc 1 n, (x + (i : ℝ) : ℝ) : ℝ) > ↑(n !) := by
      linarith
    nlinarith [show (∏ i in Finset.Icc 1 n, (x + (i : ℝ) : ℝ) : ℝ) > (↑(n !) : ℝ) from h15, h]
  have h17 : x < (1 / ↑(n !) : ℝ) := by
    have h18 : (↑(n !) : ℝ) > 0 := by positivity
    have h19 : x * (↑(n !) : ℝ) < (1 : ℝ) := h14
    have h20 : (↑(n !) : ℝ) > 0 := by positivity
    have h21 : x < (1 / ↑(n !) : ℝ) := by
      apply (lt_div_iff₀' (by positivity)).mpr
      nlinarith
    linarith
  simpa using h17