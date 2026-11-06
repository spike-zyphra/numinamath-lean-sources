import Mathlib

set_option linter.dupNamespace false
--set_option maxRecDepth 10000

namespace algebra_14222

def P (a : Fin 4 → ℕ) := (∀ i, 0 < a i) ∧ StrictMono a ∧ (∑ i, a i) / (4 : ℚ) = 4

/- The average of four different positive whole numbers is $4.$ If the difference between the largest and smallest of these numbers is as large as possible, what is the average of the other two numbers? -/
theorem algebra_14222 (a : Fin 4 → ℕ)
    (ha : P a) (hmaxdiff : IsGreatest {x | ∃ a, P a ∧ x = a 3 - a 0} (a 3 - a 0)) :
    (a 1 + a 2) / (2 : ℚ) = 5 / 2 := by
  have bounds a (pa : P a) : a 0 + a 1 + a 2 + a 3 = 16 ∧ a 0 ≥ 1 ∧ a 1 ≥ 2 ∧ a 2 ≥ 3 ∧ a 3 ≤ 10 ∧ a 3 - a 0 ≤ 9 := by
    rcases pa with ⟨a_pos, strictMono_a, a_avg_eq⟩
    -- Since the average of four numbers is $4,$ their sum is $4 \times 4 = 16.$
    have : a 0 + a 1 + a 2 + a 3 = 16 := by
      have : ∑ i, a i = 16 := by
        field_simp at a_avg_eq
        norm_num at a_avg_eq
        norm_cast at a_avg_eq
      convert this
      --exact Eq.symm (Fin.sum_univ_four a) -- This works but I want to try something more general.
      --dsimp [Finset.sum] -- "maximum recursion depth has been reached"
      simp [Finset.sum]
      --norm_num -- doesn't evaluate `Fin.succ 2` to 3.
      have : Fin.succ (2 : Fin 3) = 3 := rfl
      rw [this]
      ring
    use this
    /-
    For the difference between the largest and smallest of these numbers to be as large as possible, we would like one of the numbers to be as small as possible (so equal to $1$) and the other (call it $B$ for big) to be as large as possible.

    Since one of the numbers is $1,$ the sum of the other three numbers is $16-1=15.$
     -/
    --have := Fintype.elems (α := Fin 4).image a_pos
    have := a_pos 0
    have : a 0 ≥ 1 := by omega
    constructor
    . assumption
    have := strictMono_a (show 0 < 1 by simp)
    have : a 1 ≥ 2 := by omega
    constructor
    . assumption
    have := strictMono_a (show 1 < 2 by simp)
    have : a 2 ≥ 3 := by omega
    constructor
    . assumption
    have : a 3 ≤ 10 := by linarith
    constructor
    . assumption
    . omega -- `linarith` doesn't work
  have diff_le_9 a (pa : P a) : a 3 - a 0 ≤ 9 :=
    (bounds a pa).2.2.2.2.2
  have ex_eq_bound : ∃ a, P a ∧ /- a 3 - a 0 = 9 -/ 9 = a 3 - a 0 := by
    let a : Fin 4 → ℕ | 0 => 1 | 1 => 2 | 2 => 3 | 3 => 10
    use a
    constructor
    . constructor
      . intro i
        fin_cases i <;>
        . simp
      constructor
      . apply Fin.strictMono_iff_lt_succ.mpr
        intro i
        fin_cases i <;>
        . --simp [a]
          norm_num
      . --norm_num [a, Finset.sum]
        rw [Fin.sum_univ_four a]
        /-
        dsimp [a]
        rfl
         -/
        norm_num
    dsimp [a]
  have a_diff_le_9 : a 3 - a 0 ≤ 9 :=
    diff_le_9 a ha
  --rcases ex_eq_bound with ⟨b, ⟨pb, b_diff_eq⟩⟩
  dsimp [IsGreatest, upperBounds] at hmaxdiff
  rcases hmaxdiff with ⟨_, a_diff_ge_any⟩
  have a_diff_ge_9 : a 3 - a 0 ≥ 9 :=
    a_diff_ge_any ex_eq_bound
  -- For the $B$ to be as large as possible, we must make the remaining two numbers (which must be different and not equal to $1$) as small as possible. So these other two numbers must be equal to $2$ and $3,$ which would make $B$ equal to $15-2-3 = 10.$
  have : a 3 - a 0 = 9 := by omega
  rcases bounds a ha
  have : a 0 = 1 := by omega
  have a1_eq : a 1 = 2 := by omega
  have a2_eq : a 2 = 3 := by omega
  rw [a1_eq, a2_eq]
  -- So the average of these other two numbers is $\dfrac{2+3}{2}=\dfrac{5}{2}$ or $\boxed{2\frac{1}{2}}.$
  --rfl
  --dsimp
  --simp
  norm_num

end algebra_14222
open algebra_14222
