import Mathlib
open Mathlib

/--
Francesca uses 100 grams of lemon juice, 100 grams of sugar, and 400 grams of water to make lemonade.  There are 25 calories in 100 grams of lemon juice and 386 calories in 100 grams of sugar.  Water contains no calories.  How many calories are in 200 grams of her lemonade?
$\text {(A) } 129 \qquad \text {(B) } 137 \qquad \text {(C) } 174 \qquad \text {(D) } 223 \qquad \text {(E) } 411$
-/
lemma algebra_1176 (lemonJuice : ℚ) (sugar : ℚ) (water : ℚ) (h1 : lemonJuice = 100) (h2 : sugar = 100) (h3 : water = 400) (lemonJuiceCalories sugarCalories waterCalories : ℚ) (h4 : lemonJuiceCalories = 25 * lemonJuice / 100) (h5 : sugarCalories = 386 * sugar / 100) (h6 : waterCalories = 0) : (lemonJuiceCalories + sugarCalories + waterCalories) / (lemonJuice + sugar + water) * 200 = 137 := by
  -- Francesca makes a total of $100+100+400=600$ grams of lemonade
  rw [h1, h2, h3]
  norm_num
  -- and in those $600$ grams, there are $25$ calories from the lemon juice and $386$ calories from the sugar, for a total of $25+386=411$ calories per $600$ grams
  rw [h4, h5, h6, h1, h2]
  -- We want to know how many calories there are in $200=600/3$ grams, so we just divide $411$ by $3$ to get $137\implies\boxed{(\text{B})}$.
  norm_num