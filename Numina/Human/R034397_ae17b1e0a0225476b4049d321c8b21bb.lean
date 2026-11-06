import Mathlib

/-A 420-page book contains an average of 600 words per page, and Roslyn reads the book at the rate of 360 words per minute. How many hours did it take her to read the book? Express your answer as a mixed number.-/
theorem algebra_20639 (total_pages : ℕ) (words_per_page : ℕ) (reading_rate : ℕ)
    (h₀ : total_pages = 420) (h₁ : words_per_page = 600) (h₂ : reading_rate = 360) :
    total_pages * words_per_page / (60 * reading_rate) =(11 + 2 / 3 : ℝ):= by
      -- This book contains $420\times 600 = 252000$ words. Roslyn reads at 360 words per minute, so it takes her $\frac{252000}{360} = 700$ minutes to read the book. To find how many hours it took her, we divide by 60: $\frac{700}{60} = \boxed{11 \frac{2}{3}}$.
      norm_num [h₀, h₁, h₂]