#pragma once

#include <vector>
#include <algorithm>
#include <cassert>

namespace ratio
{

template <typename T>
std::vector<std::vector<T>> cartesian_product(const std::vector<std::vector<T>> &vs)
{
    assert(std::none_of(vs.begin(), vs.end(), [&](const std::vector<T> v) { return v.empty(); }));
    std::vector<typename std::vector<T>::const_iterator> it;
    it.reserve(vs.size());
    for (const auto &v : vs)
        it.push_back(v.cbegin());

    std::vector<std::vector<T>> s;
    while (it[0] != vs[0].cend())
    {
        std::vector<T> c_v;
        for (const auto &i : it)
            c_v.push_back(*i);
        s.push_back(c_v);

        ++it[vs.size() - 1];
        for (size_t i = vs.size() - 1; (i > 0) && (it[i] == vs[i].cend()); --i)
        {
            it[i] = vs[i].cbegin();
            ++it[i - 1];
        }
    }
    return s;
}
}