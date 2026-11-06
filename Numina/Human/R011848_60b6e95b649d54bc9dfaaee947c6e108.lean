import Mathlib

/- A is a two-digit number and B is a three-digit number such that A increased by B% equals B reduced by A%. Find all possible pairs (A, B). -/
theorem algebra_64758 {A B : ℕ} (hA : A ∈ Finset.Icc 10 99) (hB : B ∈ Finset.Icc 100 999) :
    A * (1 + B / 100 : ℚ) = B * (1 - A / 100 : ℚ) ↔
    (A, B) ∈ ({(40, 200), (45, 450), (46, 575)} : Finset (ℕ × ℕ)) := by
  constructor
  . intro h
    -- Actually, $50-A$ can be a one-digit number as well (it is $A$ that has to be two-digits), so we also have to check the cases $50-A\in\\{1,2,4,5\\}$ corresponding to $50+B\in\\{2500,1250,625, 500\\}$ . The last two give three-digit numbers for $B$ .
    have mul_eq : (50 - A) * (50 + B) = 2500 := by
      -- `omega` would work if it were `ℚ` here.
      have eq_ℤ : ((50 - A) * (50 + B) : ℤ) = 2500 := by
        qify
        linarith
      have : (50 - A : ℤ) ≥ 0 := by nlinarith
      have : (50 - A : ℕ) = (50 - A : ℤ) := by omega
      zify
      rw [this]
      exact eq_ℤ
    have : 50 - A > 2 ∧ 50 - A < 17 := by
      simp at hA hB
      constructor <;>
      . nlinarith
    have : 50 - A ∣ 2500 := by
      exact Dvd.intro (50 + B) mul_eq
    have : 50 - A ∈ (Finset.Ioo 2 17).filter (fun d => d ∣ 2500) := by
      simp
      constructor <;> assumption
    rw [show (Finset.Ioo 2 17).filter (fun d => d ∣ 2500) = {4, 5, 10} from rfl /- by native_decide -/] at this
    -- Thus the solutions are $(A,B)\in\\{(40,200), (45,450), (46,575)\\}$ .
    generalize _50_sub_a_eq : 50 - A = d at this
    fin_cases this
    . rw [show A = 46 by omega, show B = 575 by nlinarith]
      decide
    . rw [show A = 45 by omega, show B = 450 by nlinarith]
      decide
    . rw [show A = 40 by omega, show B = 200 by nlinarith]
      decide
  . intro A_B_in
    fin_cases A_B_in <;>
    . norm_num
