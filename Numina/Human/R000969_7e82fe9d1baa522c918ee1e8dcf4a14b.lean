import Mathlib

/- Sam decides to start a rumor. Sam tells the rumor to her three friends. Each of Sam's three friends then tells the rumor to three friends who have not heard the rumor. This continues for five total cycles. Sam telling her three friends was the first cycle. How many people, not including Sam, will have heard the rumor when the fifth cycle is complete? -/
theorem algebra_19473 (n : ℕ) (h : n = 5) :
    ∑ i ∈ Finset.Icc 1 n, 3 ^ i = 363 := by subst n; native_decide
