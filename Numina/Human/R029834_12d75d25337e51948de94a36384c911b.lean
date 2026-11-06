import Mathlib

/- a) the last digit in the decimal expansion of \(7^{1000}\)-/
theorem number_theory_4852_1 {a n : ℕ} (ha : a = 7) (hn : n = 10) : a^1000 ≡ 1 [MOD n] := by
--    First, we calculate \(\phi(10)\):
-- \[
-- \phi(10) = 10 \left(1 - \frac{1}{2}\right)\left(1 - \frac{1}{5}\right) = 10 \cdot \frac{1}{2} \cdot \frac{4}{5} = 4.
-- \]
  have hnt : n.totient = 4 := hn ▸ by decide
  have hacon : a.Coprime n := ha ▸ hn ▸ by norm_num
--    Since \(7\) and \(10\) are coprime, we can apply Euler's theorem:
-- \[
-- 7^4 \equiv 1 \mod 10.
-- \]
  haveI := Nat.ModEq.pow_totient hacon
  haveI := Nat.ModEq.pow 250 this
--    Next, we find \(1000 \mod 4\):
-- \[
-- 1000 \div 4 = 250 \quad \text{(remainder 0)} \quad \Rightarrow \quad 1000 \equiv 0 \mod 4.
-- \]
-- Thus, we have:
-- \[
-- 7^{1000} \equiv (7^4)^{250} \equiv 1^{250} \equiv 1 \mod 10.
-- \]
  rwa [hnt, ← pow_mul, show 4*250=1000 by norm_num, one_pow] at this

/- b) the last digit in the hexadecimal expansion of \(5^{1000000}\)-/
theorem number_theory_4852_2 {a n : ℕ} (ha : a = 5) (hn : n = 16) : a^1000000 ≡ 1 [MOD n] := by
--    Again, we use Euler's theorem. First, we calculate \(\phi(16)\):
-- \[
-- \phi(16) = 16 \left(1 - \frac{1}{2}\right) = 16 \cdot \frac{1}{2} = 8.
-- \]
  have hnt : n.totient = 8 := hn ▸ by decide
  have hacon : a.Coprime n := ha ▸ hn ▸ by norm_num
--    Since \(5\) and \(16\) are coprime, we can apply Euler's theorem:
-- \[
-- 5^8 \equiv 1 \mod 16.
-- \]
  haveI := Nat.ModEq.pow_totient hacon
  haveI := Nat.ModEq.pow 125000 this
  set N := 125000 with hN
--    Next, we find \(1000000 \mod 8\):
-- \[
-- 1000000 \div 8 = 125000 \quad \text{(remainder 0)} \quad \Rightarrow \quad 1000000 \equiv 0 \mod 8.
-- \]
-- Thus, we have:
-- \[
-- 5^{1000000} \equiv (5^8)^{125000} \equiv 1^{125000} \equiv 1 \mod 16.
-- \]
  rwa [hnt, ← pow_mul, show 8*N=1000000 by norm_num, one_pow] at this
