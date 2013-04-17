// Copyright (c) 2013 Radek Micek

var decodeEntities = (function() {
  var el = document.createElement('div');

  function decodeInternal (str) {
    if(str && typeof str === 'string') {
      str = str.replace(/</g, '&lt;');
      str = str.replace(/>/g, '&gt;');
      el.innerHTML = str;
      str = el.textContent;
      el.textContent = '';
    }

    return str;
  }

  return decodeInternal;
})();

var EVAL = function (a0) {
  var ev = __IDRRT__.tailcall(function () {
    return __IDR__.EVAL0(a0);
  });
  return ev;
};

var APPLY1 = function (f, a0) {
  var ap = __IDRRT__.tailcall(function () {
    return __IDR__.APPLY0(f, a0);
  });
  return EVAL(ap);
};

var APPLY2 = function (f, a0, a1) {
  var ap = __IDRRT__.tailcall(function () {
    return __IDR__.APPLY0(__IDR__.APPLY0(f, a0), a1);
  });
  return EVAL(ap);
};

var promptHelper = function (msg, mkNothing, mkJust) {
  var result = prompt(msg);
  if (result === null) {
    return APPLY1(mkNothing, undefined);
  }
  else {
    return APPLY1(mkJust, result);
  }
};

var getNth = function (arr, i) {
  return arr[i];
};

var setNth = function (arr, i, val) {
  arr[i] = val;
};

var anyA = function (f, arr) {
  var res = arr.some(function (x) {
    return APPLY1(f, x);
  });

  return res ? 1 : 0;
};

var filterA = function (f, arr) {
  return arr.filter(function (x) {
    return APPLY1(f, x);
  });
};

var d3Root = function () {
  return window.d3;
};

var attrPrime = function (sel, attr, f) {
  return sel.attr(attr, function (d, i) {
    return APPLY2(f, d, i);
  });
};

var classedPrime = function (sel, cls, f) {
  return sel.classed(cls, function (d, i) {
    return APPLY2(f, d, i);
  });
};

var stylePrime = function (sel, name, f) {
  return sel.style(name, function (d, i) {
    return APPLY2(f, d, i);
  });
};

var boolProperty = function (sel, name, val) {
  return sel.property(name, val ? true : false);
};

var getBoolProperty = function (sel, name) {
  return sel.property(name) ? 1 : 0;
};

var propertyPrime = function (sel, name, f) {
  return sel.property(name, function (d, i) {
    return APPLY2(f, d, i);
  });
};

var textPrime = function (sel, f) {
  return sel.text(function (d, i) {
    return APPLY2(f, d, i);
  });
};

var htmlPrime = function (sel, f) {
  return sel.html(function (d, i) {
    return APPLY2(f, d, i);
  });
};

var bindPrime = function (sel, f) {
  return sel.data(function (d, i) {
    return APPLY2(f, d, i);
  });
};

var bindK = function (sel, arr, key) {
  return sel.data(arr, function (d, i) {
    return APPLY2(key, d, i);
  });
};

var bindKPrime = function (sel, f, key) {
  return sel.data(
    function (d, i) {
      return APPLY2(f, d, i);
    },
    function (d, i) {
      return APPLY2(key, d, i);
    }
  );
};

var onClick = function (sel, handler) {
  sel.on("click", function () {
    return APPLY1(handler, undefined);
  });
};

var mkNode = function (d) {
  return { data : d };
};

var mkLink = function (src, tgt, d) {
  return { source : src, target : tgt, data : d };
};

var mkForceLayout = function (width, height) {
  return window.d3.layout.force().size([width, height]);
};

var getWidthL = function (fl) {
  return fl.size()[0];
};

var getHeightL = function (fl) {
  return fl.size()[1];
};

var onTickL = function (fl, handler) {
  fl.on("tick", function () {
    return APPLY1(handler, undefined);
  });
};

var makeDraggableL = function (sel, fl) {
  return sel.call(fl.drag);
};
