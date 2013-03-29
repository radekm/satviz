// Copyright (c) 2013 Radek Micek

var promptHelper = function (msg, mkNothing, mkJust) {
  var result = prompt(msg);
  if (result === null) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(mkNothing, undefined);
    });
  }
  else {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(mkJust, result);
    });
  }
}

var getNth = function (arr, i) {
  return arr[i];
}

var setNth = function (arr, i, val) {
  arr[i] = val;
}

var d3Root = function () {
  return window.d3;
}

var attrPrime = function (sel, attr, f) {
  return sel.attr(attr, function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var classedPrime = function (sel, cls, f) {
  return sel.classed(cls, function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var stylePrime = function (sel, name, f) {
  return sel.style(name, function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var propertyPrime = function (sel, name, f) {
  return sel.property(name, function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var textPrime = function (sel, f) {
  return sel.text(function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var htmlPrime = function (sel, f) {
  return sel.html(function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var bindPrime = function (sel, f) {
  return sel.data(function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
    });
  });
}

var bindK = function (sel, arr, key) {
  return sel.data(arr, function (d, i) {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(__IDR__.APPLY0(key, d), i);
    });
  });
}

var bindKPrime = function (sel, f, key) {
  return sel.data(
    function (d, i) {
      return __IDRRT__.tailcall(function () {
        return __IDR__.APPLY0(__IDR__.APPLY0(f, d), i);
      });
    },
    function (d, i) {
      return __IDRRT__.tailcall(function () {
        return __IDR__.APPLY0(__IDR__.APPLY0(key, d), i);
      });
    }
  );
}

function onClick(sel, handler) {
  sel.on("click", function () {
    return __IDRRT__.tailcall(function () {
      return __IDR__.APPLY0(handler, undefined);
    });
  });
}
