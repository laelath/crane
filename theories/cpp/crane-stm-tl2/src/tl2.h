#pragma once

#include <any>
#include <atomic>
#include <map>
#include <set>

namespace tl2 {

enum class TL2Error {
    Failure,
    Retry,
};

template<typename>
class TVar;

class Transaction {
public:
    Transaction();

private:
    std::set<std::shared_ptr<std::any>> read_set;
    std::map<std::shared_ptr<std::any>, std::any> write_map;
    uint64_t read_version;

    template<typename>
    friend class TVar;
};

template <typename T>
class TVar {
public:
    TVar(T inital_value);
    T read(Transaction& tx);
    void write(Transaction& tx, T new_value);
private:
    T value;
    // msb is the lock bit
    // locking is done by a fetch_or with 2^63
    // ensures that if it is locked, it will be greater than any clock value
    std::atomic_uint64_t write_version;
};

}
