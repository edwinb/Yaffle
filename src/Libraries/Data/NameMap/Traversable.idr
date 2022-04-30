module Libraries.Data.NameMap.Traversable

import Core.Core
import Core.TT.Name
import Libraries.Data.NameMap

treeTraverse : (Name -> a -> CoreE err b) -> Tree h a -> CoreE err (Tree h b)
treeTraverse f (Leaf k v) = Leaf k <$> f k v
treeTraverse f (Branch2 l k r) =
    (\l', r' => Branch2 l' k r')
    <$> treeTraverse f l
    <*> treeTraverse f r
treeTraverse f (Branch3 l k1 m k2 r) =
    (\l', m', r' => Branch3 l' k1 m' k2 r')
    <$> treeTraverse f l
    <*> treeTraverse f m
    <*> treeTraverse f r

export
traverseNameMap : (Name -> a -> CoreE err b) -> NameMap a -> CoreE err (NameMap b)
traverseNameMap f Empty = pure Empty
traverseNameMap f (M h t) = M h <$> treeTraverse f t
