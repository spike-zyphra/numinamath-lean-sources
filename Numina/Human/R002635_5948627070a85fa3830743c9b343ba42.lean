import Batteries.Data.Rat.Basic
import Mathlib.Data.List.Range

/-- Let $S$ be the sum of all numbers of the form $a/b,$ where $a$ and $b$ are [relatively prime](https://artofproblemsolving.com/wiki/index.php/Relatively_prime) positive [divisors](https://artofproblemsolving.com/wiki/index.php/Divisor) of $1000.$ What is the [greatest integer](https://artofproblemsolving.com/wiki/index.php/Floor_function) that does not exceed $S/10$? -/
theorem number_theory_712 :
    Rat.floor
    (((List.range 1001) ×ˢ (List.range 1001)
    |>.filter (fun (a, b) => a ∣ 1000 ∧ b ∣ 1000 ∧ a.Coprime b)
    |>.map (fun (a, b) => (a : Rat) / (b : Rat))
    |>.sum) / 10) = 248 := by
  native_decide