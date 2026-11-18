import Practice.Cmd
import Practice.Free

-- abbrev WhatIsYourNamePrompt : Cmd Unit := Cmd.putLine "What is your name?"
-- abbrev GetLine : Cmd String := Cmd.getLine
-- abbrev Prompt : String -> Cmd Unit := Cmd.putLine

-- def main : IO Unit := do
--     handleIO WhatIsYourNamePrompt
--     let name : String ← handleIO GetLine
--     handleIO (Prompt s!"Hello {name}")

def main : IO Unit := runIO freeHello'
