import Mathlib

theorem number_theory_156441 (n : ℕ) (h₀ : n < 10^2019) (h₁ : ∀ i, 13 ∣ (n / 10^i) % 100) (h₂ : (n / 10^2018) % 10 = 6) :
    n % 10 = 2 := by
  -- For i = 2018: (n / 10^2018) % 100 must be divisible by 13.
  have h3 := h₁ 2018
  -- n < 10^2019, so n / 10^2019 = 0. Then (n / 10^2019) % 100 = 0 % 100 = 0, so 13 divides 0, which is true.
  -- Let's think of the implications of h₁.
  -- For i = 0: 13 ∣ (n / 1) % 100, so 13 ∣ n % 100
  -- For i = 1: 13 ∣ (n / 10) % 100
  -- For i = 2: 13 ∣ (n / 100) % 100
  -- ...
  -- For i = 2018: 13 ∣ (n / 10^2018) % 100
  -- Similarly, we know from h₂ that (n / 10^2018) % 10 = 6. So, the number formed by the last two digits (when divided by 10^2018) must be divisible by 13 and its last digit is 6.
  -- Let's think of the implications of h₁ for i = 2018.
  have h4 : (n / 10^2018) % 100 = 26 := by
    omega
  -- once we know that (n / 10^2018) % 100 = 26, we can extract that the digit is 2
  have h5 : (n / 10^2018) % 10 = 2 := by
    omega
  -- The key observation is that the digits repeat in a cycle of 3. Each step provides divisibility by 13.
  -- Similarly, each digit cycles in a pattern of 6, 5, 2. The last digit, at index 2018, is (2018) % 3 = 2.
  -- So the last digit is 2.
  have h6 : n % 10 = 2 := by
    have h7 := h₁ 1
    have h8 := h₁ 0
    omega
  exact h6