import Game.Levels.TermWorld

-- Here's what we'll put on the title screen
Title "Lambda Calculus Game"
Introduction
"
# Welcome to the Lambda Calculus Game!

In this game we will define and prove properties of the untyped and simply typed
lambda calculus. We assume as a prerequisite some familiarity with Lean, but not
much more than is present in the [Natural Number
Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4).
"

Info "
## Credits

* **Authors**: Chris Henson
* **Game Engine**: Jon Eugster, Alexander Bentkamp, Patrick Massot
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "An introduction to formalized metatheory"
CaptionLong "In this game you will prove properties of the untyped and simply
typed lambda calculus. Topics include type safety, confluence, and an
introduction to semantics."
Prerequisites "Natural Number Game" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
