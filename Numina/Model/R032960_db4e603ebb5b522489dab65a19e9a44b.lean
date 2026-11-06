import Mathlib

theorem number_theory_193559 (a b c d e f : ℤ) :
    13 ∣ a^12 + b^12 + c^12 + d^12 + e^12 + f^12 → 13^6 ∣ a * b * c * d * e * f := by 
  intro h
  have h1 : a % 13 = 0 ∨ a % 13 = 1 ∨ a % 13 = 2 ∨ a % 13 = 3 ∨ a % 13 = 4 ∨ a % 13 = 5 ∨ a % 13 = 6 ∨ a % 13 = 7 ∨ a % 13 = 8 ∨ a % 13 = 9 ∨ a % 13 = 10 ∨ a % 13 = 11 ∨ a % 13 = 12 := by 
    omega
  have h2 : b % 13 = 0 ∨ b % 13 = 1 ∨ b % 13 = 2 ∨ b % 13 = 3 ∨ b % 13 = 4 ∨ b % 13 = 5 ∨ b % 13 = 6 ∨ b % 13 = 7 ∨ b % 13 = 8 ∨ b % 13 = 9 ∨ b % 13 = 10 ∨ b % 13 = 11 ∨ b % 13 = 12 := by 
    omega
  have h3 : c % 13 = 0 ∨ c % 13 = 1 ∨ c % 13 = 2 ∨ c % 13 = 3 ∨ c % 13 = 4 ∨ c % 13 = 5 ∨ c % 13 = 6 ∨ c % 13 = 7 ∨ c % 13 = 8 ∨ c % 13 = 9 ∨ c % 13 = 10 ∨ c % 13 = 11 ∨ c % 13 = 12 := by 
    omega
  have h4 : d % 13 = 0 ∨ d % 13 = 1 ∨ d % 13 = 2 ∨ d % 13 = 3 ∨ d % 13 = 4 ∨ d % 13 = 5 ∨ d % 13 = 6 ∨ d % 13 = 7 ∨ d % 13 = 8 ∨ d % 13 = 9 ∨ d % 13 = 10 ∨ d % 13 = 11 ∨ d % 13 = 12 := by 
    omega
  have h5 : e % 13 = 0 ∨ e % 13 = 1 ∨ e % 13 = 2 ∨ e % 13 = 3 ∨ e % 13 = 4 ∨ e % 13 = 5 ∨ e % 13 = 6 ∨ e % 13 = 7 ∨ e % 13 = 8 ∨ e % 13 = 9 ∨ e % 13 = 10 ∨ e % 13 = 11 ∨ e % 13 = 12 := by 
    omega
  have h6 : f % 13 = 0 ∨ f % 13 = 1 ∨ f % 13 = 2 ∨ f % 13 = 3 ∨ f % 13 = 4 ∨ f % 13 = 5 ∨ f % 13 = 6 ∨ f % 13 = 7 ∨ f % 13 = 8 ∨ f % 13 = 9 ∨ f % 13 = 10 ∨ f % 13 = 11 ∨ f % 13 = 12 := by 
    omega
  have ha12 : a^12 % 13 = 0 ∨ a^12 % 13 = 1 := by
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] 
  have hb12 : b^12 % 13 = 0 ∨ b^12 % 13 = 1 := by 
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] 
  have hc12 : c^12 % 13 = 0 ∨ c^12 % 13 = 1 := by 
    rcases h3 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] 
  have hd12 : d^12 % 13 = 0 ∨ d^12 % 13 = 1 := by 
    rcases h4 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] 
  have he12 : e^12 % 13 = 0 ∨ e^12 % 13 = 1 := by 
    rcases h5 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] 
  have hf12 : f^12 % 13 = 0 ∨ f^12 % 13 = 1 := by 
    rcases h6 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] 
  have h7 : (a^12 + b^12 + c^12 + d^12 + e^12 + f^12) % 13 = 0 := by 
    omega
  have h8 : (a^12 % 13 + b^12 % 13 + c^12 % 13 + d^12 % 13 + e^12 % 13 + f^12 % 13) % 13 = 0 := by 
    omega
  have h9 : a^12 % 13 = 0 := by 
    omega
  have h10 : b^12 % 13 = 0 := by 
    omega
  have h11 : c^12 % 13 = 0 := by 
    omega
  have h12 : d^12 % 13 = 0 := by 
    omega
  have h13 : e^12 % 13 = 0 := by 
    omega
  have h14 : f^12 % 13 = 0 := by 
    omega
  have h15 : a % 13 = 0 := by 
    rcases h1 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] at h9 <;> tauto
  have h16 : b % 13 = 0 := by 
    rcases h2 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] at h10 <;> tauto
  have h17 : c % 13 = 0 := by 
    rcases h3 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] at h11 <;> tauto
  have h18 : d % 13 = 0 := by 
    rcases h4 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] at h12 <;> tauto
  have h19 : e % 13 = 0 := by 
    rcases h5 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] at h13 <;> tauto
  have h20 : f % 13 = 0 := by 
    rcases h6 with (h | h | h | h | h | h | h | h | h | h | h | h | h) <;> norm_num [pow_succ, Int.mul_emod, h] at h14 <;> tauto
  have h21 : 13 ∣ a := by 
    omega
  have h22 : 13 ∣ b := by 
    omega
  have h23 : 13 ∣ c := by 
    omega
  have h24 : 13 ∣ d := by 
    omega
  have h25 : 13 ∣ e := by 
    omega
  have h26 : 13 ∣ f := by 
    omega
  obtain ⟨k, hk⟩ := h21
  obtain ⟨l, hl⟩ := h22
  obtain ⟨m, hm⟩ := h23
  obtain ⟨n, hn⟩ := h24
  obtain ⟨p, hp⟩ := h25
  obtain ⟨q, hq⟩ := h26
  use k * l * m * n * p * q
  rw [hk, hl, hm, hn, hp, hq]
  ring