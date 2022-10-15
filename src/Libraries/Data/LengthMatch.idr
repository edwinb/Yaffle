module Libraries.Data.LengthMatch

%default total

public export
data LengthMatch : SnocList a -> SnocList b -> Type where
     LinMatch : LengthMatch [<] [<]
     SnocMatch : LengthMatch xs ys -> LengthMatch (xs :< x) (ys :< y)

export
checkLengthMatch : (xs : SnocList a) -> (ys : SnocList b) ->
                   Maybe (LengthMatch xs ys)
checkLengthMatch [<] [<] = Just LinMatch
checkLengthMatch [<] (xs :< x) = Nothing
checkLengthMatch (xs :< x) [<] = Nothing
checkLengthMatch (xs :< x) (ys :< y)
    = Just (SnocMatch !(checkLengthMatch xs ys))

export
lengthsMatch : LengthMatch xs ys -> (length xs) = (length ys)
lengthsMatch LinMatch = Refl
lengthsMatch (SnocMatch x) = cong (S) (lengthsMatch x)
