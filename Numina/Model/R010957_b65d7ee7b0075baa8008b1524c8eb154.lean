import Mathlib

def D := Nat.divisors 100
def Z := Finset.Icc 1 100

theorem number_theory_609244 :
    ((D ×ˢ Z).filter (fun (d, z) => d ∣ z)).card / (D.card * Z.card) = (217 / 900 : ℚ) := by 
  have h1 : D.card = 9 := by 
    native_decide 
  have h2 : Z.card = 100 := by 
    native_decide 
  have h3 : ((D ×ˢ Z).filter (fun (d, z) => d ∣ z)).card = 217 := by 
    native_decide 
  have h4 : D.card * Z.card = 900 := by 
    calc 
      D.card * Z.card = 9 * 100 := by 
        rw [h1, h2]
      _ = 900 := by 
        norm_num 
  have eq1 : ( ( ((D ×ˢ Z).filter (fun (d, z) => d ∣ z)).card ) : ℚ ) = (217 : ℚ) := by
    exact_mod_cast h3
  have eq2 : ( (D.card * Z.card) : ℚ ) = (900 : ℚ) := by
    exact_mod_cast h4
  rw [eq1, eq2] 
  all_goals norm_num