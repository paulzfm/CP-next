--> "Version 0.1: usage..."

interface Editor {
  onKey: String -> String;
  doCut: String;
  showHelp: String;
};

interface Version { version : String };

editor = trait [self : Editor & Version] implements Editor => {
  onKey = \key -> "Pressing " ++ key;
  doCut = onKey "C-x" ++ " for cutting text";
  showHelp = "Version " ++ version ++ ": usage...";
};

version = trait implements Version => { version = "0.1" };

(new editor , version).showHelp
