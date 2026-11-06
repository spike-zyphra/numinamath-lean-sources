import Mathlib
theorem algebra_1142 (socks_cost tshirt_cost member_cost total_cost : ℚ) (num_members : ℕ) (hsocks_cost : socks_cost = 4) (htshirt_cost : tshirt_cost = socks_cost + 5) (hmember_cost : member_cost = socks_cost + tshirt_cost + socks_cost + tshirt_cost) (htotal_cost' : total_cost = 2366) (htotal_cost : total_cost = member_cost * num_members) : num_members = 91 := by
  have htshirt : tshirt_cost = 9 := by
    rw [hsocks_cost] at htshirt_cost
    linarith
  have hmember : member_cost = 26 := by
    rw [hmember_cost, hsocks_cost, htshirt]
    norm_num
  have eq1 : (num_members : ℚ) = 91 := by
    rw [hmember] at htotal_cost
    rw [htotal_cost'] at htotal_cost
    linarith
  exact_mod_cast eq1