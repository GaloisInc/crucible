#include <iostream>
#include <string>
void cxxbasic(int arg) {
  std::string foo = "bar";

  if (arg % 2) {
    std::cout << "foo=" << foo << '\n';
  } else {
    foo = "baz";
  }

  std::cout << "foo=" << foo << '\n';
}
