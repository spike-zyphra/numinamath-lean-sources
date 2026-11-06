import Mathlib

/- Kereste Silenost Bacchus ... He did not find him,

His weariness he rested somewhere in the shade.

"In vain let time not pass," he thought.

He himself sat down in a boxwood thicket.

And he gestured to Melampus ... showing his cup

He reached the goblet and struck a new cask with a blow.

(It was a pair to the one that lay empty there, From which Silenus had drunk every last drop.)

Mopsus and Melitta began a cheerful song

Joyful praises rang out to the god.

Bacchus just drank ... clicking his tongue ...

His face turned red, his mood became fiery.

"Well, let's leave him a few cups - he said - I know, he likes the Lemnian wine.

While the old man is still good ... look at the table here:

Calculate for me, Melampus, how long have I been drinking?"

"You know, sir: 'the rose does not grow in the marsh' ...

How should I know? ... never having learned algebra ...

But this much - he said - I can still figure out,

And in this, the natural numbers do not deceive me:

Two-thirds of that time has passed. How much does Silenus need for such a cask, To drink it dry to the last drop ... For he only rests until they are filled to the brim."

Silenus emerged ... (Melampus was still speaking.)

And he brought a full cask over.

He poured and drank the honeyed nectar of Lemnos

$S$ often thanked the merry god.

He drank all the leftovers alone.

Their songs also ended, Mopsus and Melitta.

The cask was empty ... Silence settled on the field...

Bacchus and Silenus were overcome by sleep.

Melampus calculated: ... "if they drink together ...

They would have fallen asleep two hours earlier

On such a cask. But Bacchus, how much he left behind, It would be just half of it."

The speech was a riddle to the beautiful Melitta,

Mopsus did not understand it either and would still be calculating,

If Grandpa Melampus did not tell them.

$-------------10$

Will there be among you the one who will solve it? ...

And will say - what is most important - "if they drink separately:

How long does such a cask last for Silenus ... for Bacchus!" -/
theorem algebra_242378 (t : ℝ) (ht : t > 0) (h : (2 / 3) * t = (1 / 2) * (t - 2)) :
    t = 4 := by
  nlinarith