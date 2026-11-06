import Mathlib

open Nat

/-- In base $R_1$ the expanded fraction $F_1$ becomes $.373737\cdots$, and the expanded fraction $F_2$
becomes $.737373\cdots$. In base $R_2$ fraction $F_1$, when expanded, becomes $.252525\cdots$, while
the fraction $F_2$ becomes $.525252\cdots$. The sum of $R_1$ and $R_2$, each written in the base ten,
is:

$\text{(A) } 24 \quad \text{(B) } 22 \quad \text{(C) } 21 \quad \text{(D) } 20 \quad \text{(E) } 19$ -/
theorem number_theory_94964 {R1 R2 : ℕ} {F1 F2 : ℚ}
    (hR1 : R1 > 7) (hR2 : R2 > 7)
    (hF1 : F1 = (ofDigits R1 [7, 3]) / (ofDigits R1 [R1 - 1, R1 - 1]))
    (hF2 : F2 = (ofDigits R1 [3, 7]) / (ofDigits R1 [R1 - 1, R1 - 1]))
    (hF1' : F1 = (ofDigits R2 [5, 2]) / (ofDigits R2 [R2 - 1, R2 - 1]))
    (hF2' : F2 = (ofDigits R2 [2, 5]) / (ofDigits R2 [R2 - 1, R2 - 1])) :
    R1 + R2 = 19 := by

  -- We will show that $R_1=11$ and $R_2=8$.
  suffices R1 = 11 ∧ R2 = 8 by simp [this.1, this.2]

  -- First, let's write $F_1$ as a proper fraction in base $R_1$. To do that, note that:
  -- $F_1=0.373737\dots$ Multiplying this equation on both sides $R_1^2$, we get:
  -- $R_1^2F_1=37.373737\dots$ Subtracting the first equation from the second one, we get:
  -- $R_1^2F_1-F_1=37\\F_1(R_1^2-1)=37\\F_1=\frac{3R_1+7}{R_1^2-1}$
  replace hF1 : F1 = (7 + 3 * R1) / (R1^2 - 1) := by
    simp (discharger := omega) [hF1, ofDigits]
    ring

  -- Using a very similar method as above, we can see that:
  -- $F_1=\frac{3R_1+7}{R_1^2-1}=\frac{2R_2+5}{R_2^2-1}$ and $F_2=\frac{7R_1+3}{R_1^2-1}=
  -- \frac{5R_2+2}{R_2^2-1}$
  replace hF2 : F2 = (3 + 7 * R1) / (R1^2 - 1) := by
    simp (discharger := omega) [hF2, ofDigits]
    ring
  replace hF1' : F1 = (5 + 2 * R2) / (R2^2 - 1) := by
    simp (discharger := omega) [hF1', ofDigits]
    ring
  replace hF2' : F2 = (2 + 5 * R2) / (R2^2 - 1) := by
    simp (discharger := omega) [hF2', ofDigits]
    ring

  have : 0 < (R1:ℚ)^2 - 1 := by
    simp
    linarith only [hR1]

  have : 0 < (R2:ℚ)^2 - 1 := by
    simp
    linarith only [hR2]

  have : 0 < F2 := by
    rw [hF2]
    field_simp
    linarith only [hR1]

  -- Dividing the 2 equations to get some potential solutions, we get (note that we don't have to
  -- worry about division by zero because $R_1,R_2>7$):
  have :=
    calc (3 * R1 + 7) / (7 * R1 + 3) = (F1 * (R1^2 - 1)) / (F2 * (R1^2 - 1)) := by rw [hF1, hF2]; field_simp; ring
         _ = F1 / F2 := by field_simp; ring
         _ = (F1 * (R2^2 - 1)) / (F2 * (R2^2 - 1)) := by field_simp; ring
         _ = (2 * R2 + 5) / (5 * R2 + 2) := by rw [hF1', hF2']; field_simp; ring

  -- Then, re arranging the equation, we get:
  field_simp at this
  have hR1R2 : ((R1:ℤ) + 29) * (29 - R2) = 840 := by qify; nlinarith only [this]

  -- Becasue $R_1 + 29$ and 840 are positive, $29 - R_2$ is positive as well. This means that $R_2$
  -- is less than 29.
  have hR2' : R2 < 29 := by nlinarith only [hR1R2]
  have : 0 < 29 - R2 := by simp [hR2']
  have : (29 + R1) * (29 - R2) = 840 := by zify; push_cast [hR2']; convert hR1R2 using 1; ring

  -- This equation tells us that $29 - R_2$ is a divisor of 840. Listing the divisors of 840, the
  -- possibilities for $R_2$ are as follows:
  have hR2_mem : R2 ∈ Finset.filter (fun n ↦ 7 < n ∧ n < 29) (Finset.image (fun d ↦ 29 - d) (Nat.divisors 840)) := by
    simp
    refine ⟨?_, by assumption, by assumption⟩
    use 29 - R2
    split_ands
    · exact Dvd.intro_left (29 + R1) this
    · omega

  replace hR2_mem : R2 ∈ ({28, 27, 26, 25, 24, 23, 22, 21, 19, 17, 15, 14, 9, 8} : Finset ℕ) := by
    set_option maxRecDepth 10000 in convert hR2_mem using 1


  have hR1_eq : R1 = 840 / (29 - R2) - 29 := by
    rw [←this]
    field_simp

  -- Now, let's try each possibility for $R_2$ to see which one works.
  simp at hR2_mem
  rcases hR2_mem with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)

  -- All choices except for $R_2=8$ lead to a contradiction.
  any_goals
    simp at hR1_eq
    subst hR1_eq
    field_simp [hF1'] at hF1
    norm_num at hF1

  -- Therefore, $R_2=8$ and $R_1=11$.
  simp