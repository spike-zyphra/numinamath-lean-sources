import Mathlib

theorem number_theory_232558 :
    {(x, y, z) : ℕ × ℕ × ℕ | x * 16 + y * 17 + z * 21 = 185}.ncard = 5 := by 
  have h1 : {(x, y, z) : ℕ × ℕ × ℕ | x * 16 + y * 17 + z * 21 = 185} = Finset.filter (fun s => (s.1 * 16 + s.2.1 * 17 + s.2.2 * 21 = 185) ) (Finset.Icc (0,0,0) (11,11,8)) := by
    ext ⟨x, y, z⟩
    simp
    intro h_eq
    have hx1 : x ≤ 11 := by 
      omega
    have hy1 : y ≤ 11 := by 
      omega
    have hz1 : z ≤ 8 := by 
      omega
    omega
    all_goals
      omega
  rw [h1]
  rw [Set.ncard_coe_Finset]
  native_decide