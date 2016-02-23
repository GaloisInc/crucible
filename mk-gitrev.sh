rev=`git rev-parse HEAD`
branch=`git rev-parse --abbrev-ref HEAD`
status=`git status --porcelain`
if [ -z "$status" ] ; then
  dirty="False"
else
  dirty="True"
fi

cat > saw/GitRev.hs <<END
module GitRev (hash, branch, dirty) where

hash :: String
hash = "$rev"

branch :: String
branch = "$branch"

dirty :: Bool
dirty = $dirty
END
