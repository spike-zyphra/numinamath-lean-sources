import Mathlib
/- Let $N$ be a positive integer. For each positive integer $n$, define the function $f(n)$ as follows:
$f(n) = 0$ if $n$ is a perfect square.
$f(n) = \lfloor \frac{1}{\sqrt{n} - \lfloor\sqrt{n}\rfloor} \rfloor$ if $n$ is not a perfect square.
(where $\lfloor x \rfloor$ denotes the greatest integer not exceeding $x$).
Determine the value of $\sum_{k=1}^{N} f(k)$. For $N=8$, show the answer is 11. -/
theorem number_theory_641539 (f : ℕ → ℤ) (h1 : ∀ n : ℕ, IsSquare n → f n = 0) (h2 : ∀ n : ℕ, ¬IsSquare n → f n = ⌊1 / (√n - ⌊√n⌋)⌋) : ∑ i in Finset.range 8, f (i + 1) = 11:= by
  -- Simplify the range and apply the function definition for perfect squares (1 and 4)
  simp [Finset.range_succ]
  rw [h1 1 (by native_decide)]
  rw [h1 4 (by native_decide)]
  ring_nf

  -- Apply the function definition for non-perfect squares (2,3,5,6,7,8)
  rw [h2 2 (by native_decide)]
  rw [h2 3 (by native_decide)]
  rw [h2 5 (by native_decide)]
  rw [h2 6 (by native_decide)]
  rw [h2 7 (by native_decide)]
  rw [h2 8 (by native_decide)]

  -- Prove that floor(sqrt(2)) = 1 using bounds
  have g1 : ⌊√2⌋ = 1:= by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    simp
    simp
    have g1 : (2 : ℝ) ≤ (3 / 2) ^ 2:= by linarith
    replace g1 : √2 ≤ √((3 / 2) ^ 2):= by exact Real.sqrt_le_sqrt g1
    field_simp at g1
    linarith
  -- Prove that floor(sqrt(3)) = 1 using bounds
  have g2 : ⌊√3⌋ = 1:= by
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    simp
    simp
    have g1 : (3 : ℝ) ≤ (7 / 4) ^ 2:= by linarith
    replace g1:=  Real.sqrt_le_sqrt g1
    field_simp at g1
    linarith
  -- Prove that floor(sqrt(x)) = 2 for x = 5,6,7,8 using bounds
  have g3 : ∀ x : ℝ, x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 → ⌊√x⌋ = 2:= by
    intro x hx
    rcases hx with hx | hx | hx | hx
    all_goals
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      .
        simp
        have g1 : x ≥ 2 ^ 2:= by linarith
        replace g1:=  Real.sqrt_le_sqrt g1
        subst x
        field_simp at g1
        linarith
      .
        simp
        have g1 : x ≤ (23 / 8) ^ 2:= by linarith
        replace g1:=  Real.sqrt_le_sqrt g1
        subst x
        field_simp at g1
        linarith
  -- Apply the floor(sqrt(x)) = 2 result to specific values
  have g4:= g3 6 (by simp)
  have g5:= g3 7 (by simp)
  have g6:= g3 8 (by simp)
  replace g3:= g3 5 (by simp)
  norm_cast
  rw [g1, g2, g3, g4, g5, g6]
  norm_cast
  clear g1 g2 g3 g4 g5 g6
  -- Prove that sqrt(x) - 1 > 0 for x = 2,3 using bounds
  have g1 : ∀ x : ℝ, x = 2 ∨ x = 3 → √x - 1 > 0:= by
    intro x hx
    rcases hx with hx | hx
    all_goals
      simp
      have g1 : x ≥ (6 / 5) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Prove that sqrt(x) - 2 > 0 for x = 5,6,7,8 using bounds
  have g2 : ∀ x : ℝ, x = 5 ∨ x = 6 ∨ x = 7 ∨ x = 8 → √x - 2 > 0:= by
    intro x hx
    rcases hx with hx | hx | hx | hx
    all_goals
      simp
      have g1 : x ≥ (21 / 10) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Calculate floor(1/(sqrt(2) - 1)) = 2 using bounds
  have g3 : ⌊1 / (√2 - 1)⌋ = 2:= by
    specialize g1 2 (by simp)
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      field_simp
      suffices 2 * (√2 - 1) ≤ 1 by exact (le_div_iff₀ g1).mpr this
      have g1 : (2 : ℝ) ≤ (3 / 2) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    .
      field_simp
      suffices 1 < (2 + 1) * (√2 - 1) by exact (div_lt_iff₀ g1).mpr this
      have g1 : (2 : ℝ) ≥ (7 / 5) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Calculate floor(1/(sqrt(3) - 1)) = 1 using bounds
  have g4 : ⌊1 / (√3 - 1)⌋ = 1:= by
    specialize g1 3 (by simp)
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      field_simp
      suffices 1 * (√3 - 1) ≤ 1 by exact (le_div_iff₀ g1).mpr this
      have g1 : (3 : ℝ) ≤ 2 ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    .
      field_simp
      suffices 1 < (1 + 1) * (√3 - 1) by exact (div_lt_iff₀ g1).mpr this
      have g1 : (3 : ℝ) ≥ (8 / 5) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Calculate floor(1/(sqrt(5) - 2)) = 4 using bounds
  have g5 : ⌊1 / (√5 - 2)⌋ = 4:= by
    specialize g2 5 (by simp)
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      field_simp
      suffices 4 * (√5 - 2) ≤ 1 by exact (le_div_iff₀ g2).mpr this
      have g1 : (5 : ℝ) ≤ (9 / 4) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    .
      field_simp
      suffices 1 < (4 + 1) * (√5 - 2) by exact (div_lt_iff₀ g2).mpr this
      have g1 : (5 : ℝ) ≥ (221 / 100) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Calculate floor(1/(sqrt(6) - 2)) = 2 using bounds
  have g6 : ⌊1 / (√6 - 2)⌋ = 2:= by
    specialize g2 6 (by simp)
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      field_simp
      suffices 2 * (√6 - 2) ≤ 1 by exact (le_div_iff₀ g2).mpr this
      have g1 : (6 : ℝ) ≤ (5 / 2) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    .
      field_simp
      suffices 1 < (2 + 1) * (√6 - 2) by exact (div_lt_iff₀ g2).mpr this
      have g1 : (6 : ℝ) ≥ (12 / 5) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Calculate floor(1/(sqrt(7) - 2)) = 1 using bounds
  have g7 : ⌊1 / (√7 - 2)⌋ = 1:= by
    specialize g2 7 (by simp)
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      field_simp
      suffices 1 * (√7 - 2) ≤ 1 by exact (le_div_iff₀ g2).mpr this
      have g1 : (7 : ℝ) ≤ 3 ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    .
      field_simp
      suffices 1 < (1 + 1) * (√7 - 2) by exact (div_lt_iff₀ g2).mpr this
      have g1 : (7 : ℝ) ≥ (13 / 5) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Calculate floor(1/(sqrt(8) - 2)) = 1 using bounds
  have g8 : ⌊1 / (√8 - 2)⌋ = 1:= by
    specialize g2 8 (by simp)
    refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
    .
      field_simp
      suffices 1 * (√8 - 2) ≤ 1 by exact (le_div_iff₀ g2).mpr this
      have g1 : (8 : ℝ) ≤ 3 ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
    .
      field_simp
      suffices 1 < (1 + 1) * (√8 - 2) by exact (div_lt_iff₀ g2).mpr this
      have g1 : (8 : ℝ) ≥ (13 / 5) ^ 2:= by linarith
      replace g1:= Real.sqrt_le_sqrt g1
      field_simp at g1
      linarith
  -- Final step: combine all results to prove sum equals 11
  linarith
