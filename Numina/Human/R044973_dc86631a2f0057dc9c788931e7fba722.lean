import Mathlib


/-
Real numbers $a$ and $b$ are chosen with $1 < a < b $ such that no triangle with positive area has side lengths $1$, $a$, and $b$ or $\frac{1}{b}$, $\frac{1}{a}$, and $1$. What is the smallest possible value of $b$?
$\textbf{(A)}\ \frac{3+\sqrt{3}}{2}\qquad\textbf{(B)}\ \frac{5}{2}\qquad\textbf{(C)}\ \frac{3+\sqrt{5}}{2}\qquad\textbf{(D)}\ \frac{3+\sqrt{6}}{2}\qquad\textbf{(E)}\ 3$
-/


theorem algebra_96241 : IsLeast {b:ℝ | ∃ a, 1 < a ∧ a < b ∧
  ¬(a+b>1 ∧ b+1>a ∧ 1+a>b) ∧ ¬(1 + 1/a > 1/b ∧ 1/b + 1 > 1/a ∧ 1/a + 1/b > 1)}
  ((3 + √5)/2) := by
  -- first prove that first condition of not possible triangle is equivalent to 1 + a ≤ b
  have {p : Prop} {a b :ℝ} : 1 < a ∧ a < b ∧ ¬(a+b>1 ∧ b+1>a ∧ 1+a>b) ∧ p ↔ 1 < a ∧ a < b ∧ 1 + a ≤ b ∧ p := by
    -- push the negation and then notice that a+b > 1 and b+1 > a are easily proved from relations of a and b, hence 1 + a ≤ b
    convert_to 1 < a → a < b → p → (¬(a+b>1 ∧ b+1>a ∧ 1+a>b) ↔ 1 + a ≤ b)
    . simp
    . rintro ha hb _
      push_neg
      have aux₁ : a + b > 1 := by linarith
      have aux₂ : b + 1 > a := by linarith
      simp [aux₁, aux₂]
  simp_rw [this]

  -- next provet that second condition of not possible triangle is equivlaent to a + b ≤ ab
  have {p : Prop} {a b :ℝ} : 1 < a ∧ a < b ∧ p ∧ ¬(1 + 1/a > 1/b ∧ 1/b + 1 > 1/a ∧ 1/a + 1/b > 1) ↔ 1 < a ∧ a < b ∧ p ∧ a + b ≤ a*b := by
    -- push the negation and then notice that 1 > 1/a > 1/b, this means 1 + 1/a > 1/b and 1/b + 1 > 1/a is already proved, there fore 1/a + 1/b ≤ 1
    convert_to 1 < a → a < b → p →
      (¬(1 + 1/a > 1/b ∧ 1/b + 1 > 1/a ∧ 1/a + 1/b > 1) ↔ a + b ≤ a*b)
    . simp
    . rintro ha hb _
      push_neg
      have : 1 > 1 / a := by exact (div_lt_one (by positivity)).mpr ha
      have : 1 / a > 1 / b := by exact one_div_lt_one_div_of_lt (by positivity) hb
      have : 1 / b > 0 := by exact one_div_pos.mpr (by linarith)
      have aux₁ : 1 + 1 / a > 1 / b := by linarith
      have aux₂ : 1 / b + 1 > 1 / a := by linarith
      simp [-one_div, aux₁, aux₂]
      -- then prove that 1/a + 1/b ≤ 1 and a + b ≤ a * b are equivalent
      have : 0 < b := by linarith
      have : 0 < a * b := by apply mul_pos <;> linarith
      nth_rw 1 [Iff.symm (mul_le_mul_iff_of_pos_right this)]
      ring_nf
      field_simp
      ring_nf
  simp_rw [this]

  -- now after the simplifications, we'll prove the target
  constructor
  -- first prove (3 + √5)/2 belongs to set, use a = (1 + √5)/2 for a and show the inequalities are proved
  . use (1 + √5)/2
    have : 1 < √5 := by
      convert_to √1 < √5
      . simp
      . simp [-Real.sqrt_one, Real.sqrt_lt_sqrt]
    repeat (any_goals constructor)
    any_goals linarith
    ring_nf
    simp
    linarith
  -- next prove that inequalities imply b ≥ (3 + √5)/2, do this by getting one inequality with b (i.e. eliminating a)
  . rintro b ⟨a, ha, hb, hab₁, hab₂⟩
    -- b ≤ a(b-1) from a + b ≤ ab
    have : b ≤ a * (b - 1) := by linarith
    have : a ≤ b - 1 := by linarith
    -- a(b-1) ≤ (b-1)^2 from a + 1 ≤ b
    have : a * (b - 1) ≤ (b-1) * (b-1) := by
      have : b - 1 > 0 := by linarith
      exact (mul_le_mul_iff_of_pos_right this).mpr (by assumption)
    -- previous two together mean b ≤ (b-1)^2, this mean 5 ≤ (2b-3)^2
    have : 0 ≤ 4 * (b-1) * (b-1) - 4 * b:= by linarith
    have : 0 ≤ (2 * b - 3)^2 - 5 := by
      ring_nf at this; ring_nf; assumption
    have h : 5 ≤ (2*b - 3)^2 := by linarith
    -- due to 2b-3 > 0 (as b ≥ 1 + a > 2) we thus get √5 ≤ 2b - 3 which gets the target inequality
    convert_to (√5)^2 ≤ (2*b - 3)^2 at h
    . simp
    . have : 0 ≤ 2 * b - 3 := by linarith
      have := abs_le_of_sq_le_sq' h this
      linarith