#include "tl2.h"

namespace tl2 {

// must fit within 63 bits
std::atomic_uint64_t version_clock = 0;

Transaction::Transaction() : read_version(version_clock.load()) {};

template<typename T>
TVar<T>::TVar(T v) : value(v) {}

template<typename T>
T TVar<T>::read(Transaction& tx) {
    if (tx.write_map.contains(this)) {
        return std::any_cast<T>(tx.write_map[std::make_any(this)]);
    } else {
        T val = &this->value;
        if (this->write_version.load() > tx.read_version) {
            throw TL2Error::Failure;
        } else {
            return val;
        }
    }
};

}
