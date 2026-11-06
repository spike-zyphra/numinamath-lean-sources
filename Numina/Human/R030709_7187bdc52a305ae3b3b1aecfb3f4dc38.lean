import Mathlib

/- The Tigers beat the Sharks 2 out of the 3 times they played. They then played N more times, and the Sharks ended up winning at least 95% of all the games played. What is the minimum possible value for N?

(A) 35
(B) 37
(C) 39
(D) 41
(E) 43 -/

theorem number_theory_96875 :
  let PossibleNumber (n : ℕ) := (0 ≤ n) ∧ (∃ w: ℕ, 0 ≤ w ∧ w ≤ n ∧ (n+3) * (95: ℝ)/100 ≤ (1+w));
  PossibleNumber 37 ∧ ∀ n: ℕ, PossibleNumber n → 37 ≤ n := by
  -- split to two cases, prove 37 is a possible number and n >= 37
  apply And.intro
  -- first case, will plug in 37 and normalize to get 38 ≤ 1 + w
  . norm_num
     -- use 37 for w and normalize to prove inequality satisfied
    exists 37
    norm_num
  -- second case, will prove n >= 37
  . intro n h
    let ⟨ hn, he ⟩ := h;
    cases he with
    | intro w hw =>
      let ⟨ hwpos, ⟨ hwn, hratio ⟩⟩ := hw
      -- multiply 100 to two sides of hratio, then use w ≤ n to get (1 + w)*100 ≤ (1+n)*100, this will allow to create
      have hratio₁ : (n+3) * (95: ℝ) / 100 * 100 ≤ (1+w)*100 := by linarith
      have hwn₁ : ((1:ℝ)+w)*100 ≤ (1+n)*100 := by
        norm_num
        linarith
      have hratio₂ : (n+3) * (95:ℝ) / 100 * 100 ≤ (1+n) * 100 := le_trans hratio₁ hwn₁
      -- now manipulate inequaality to get 37 <= n
      have hratio₃ : n * 95 + 3 * (95: ℝ) ≤ 100 + n * 100 := by linarith
      have hratio₄ : (185: ℝ) ≤ n * 5:= by linarith
      have hratio₅ : (37: ℝ) ≤ (n: ℝ):= by linarith
      -- cast down from real
      exact Nat.cast_le.mp hratio₅